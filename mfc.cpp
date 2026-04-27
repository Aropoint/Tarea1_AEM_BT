// ============================================================
// MINIMAL FORWARD CHECKING (MFC)
// Heuristicas: MRV + Degree, Valor mas cercano a P_k
// Alex Marambio
// ============================================================

#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <climits>
#include <chrono>
#include <iomanip>
#include <set>
#include <numeric>
#include <atomic>
#include <thread>
#include <mutex>
#ifdef _WIN32
#include <conio.h>
#include <io.h>
#else
#include <termios.h>
#include <unistd.h>
#endif

using namespace std;
using namespace chrono;

// Estructura avón
struct Plane {
    int id;
    int E, P, L;
    double C, Cp;
};

//************************ Global variables
int D, numRunways;
vector<Plane> planes;
vector<vector<int>> sep;

vector<int> bestAssignment;
double brisKet = 1e18; //mejor costo
double prevBestCost = 1e18;
long long nodesExplored = 0;


vector<vector<int>> domains;
struct Removal { int varIdx, value; };
vector<vector<Removal>> trail;
static constexpr long long PROGRESS_EVERY = 10000LL;
time_point<high_resolution_clock> caseStartTime;

// Tiempo sin mejorar el óptimo antes de detener la búsqueda
static constexpr double TIMEOUT_NO_OPTIMUM_SEC = 3600.0;

time_point<high_resolution_clock> lastOptimumTime;
mutex                             mtxLastOptimum;

atomic<bool> timeoutFired{false};
atomic<bool> searchActive{false};
atomic<bool> userInterrupt{false};

struct TimeoutOptimum {};

// El perrowacho que vigila tiempo sin nuevo óptimo y activa timeoutFired
void watchdogThread() {
    using ms_t = duration<double, milli>;
    while (searchActive.load(memory_order_acquire)) {
        this_thread::sleep_for(milliseconds(500));
        if (!searchActive.load(memory_order_acquire)) break;

        time_point<high_resolution_clock> tOpt;
        {
            lock_guard<mutex> lk(mtxLastOptimum);
            tOpt = lastOptimumTime;
        }
        double sinceOptimum =
            duration_cast<ms_t>(high_resolution_clock::now() - tOpt).count()
            / 1000.0;
        if (sinceOptimum >= TIMEOUT_NO_OPTIMUM_SEC) {
            timeoutFired.store(true, memory_order_release);
            break;
        }
    }
}

// ── Keyboard listener thread ─────────────────────────────────
void keyboardThread() {
#ifdef _WIN32
    while (searchActive.load(memory_order_acquire)) {
        if (_kbhit()) {
            int ch = _getch();
            if (ch == 'q' || ch == 'Q') {
                userInterrupt.store(true, memory_order_release);
                break;
            }
        }
        this_thread::sleep_for(milliseconds(50));
    }
#else
    struct termios oldTerm, rawTerm;
    bool isaTTY = isatty(STDIN_FILENO);
    if (isaTTY) {
        tcgetattr(STDIN_FILENO, &oldTerm);
        rawTerm = oldTerm;
        rawTerm.c_lflag &= ~(ICANON | ECHO);
        rawTerm.c_cc[VMIN]  = 0;
        rawTerm.c_cc[VTIME] = 1;
        tcsetattr(STDIN_FILENO, TCSANOW, &rawTerm);
    }

    while (searchActive.load(memory_order_acquire)) {
        char c = 0;
        if (isaTTY) {
            ssize_t n = read(STDIN_FILENO, &c, 1);
            if (n <= 0) { this_thread::sleep_for(milliseconds(10)); continue; }
        } else {
            fd_set fds;
            FD_ZERO(&fds);
            FD_SET(STDIN_FILENO, &fds);
            struct timeval tv = {0, 100000};
            int ret = select(STDIN_FILENO + 1, &fds, nullptr, nullptr, &tv);
            if (ret <= 0) continue;
            ssize_t n = read(STDIN_FILENO, &c, 1);
            if (n <= 0) { this_thread::sleep_for(milliseconds(10)); continue; }
        }
        if (c == 'q' || c == 'Q') {
            userInterrupt.store(true, memory_order_release);
            break;
        }
    }

    if (isaTTY) tcsetattr(STDIN_FILENO, TCSANOW, &oldTerm);
#endif
}

// **************************************************Funciones útiles
double computeCost(const Plane& av, int t) {
    if (t < av.P) return av.C  * (av.P - t);
    if (t > av.P) return av.Cp * (t - av.P);
    return 0.0;
}

void initDomains() {
    // Paso 1: agregar E_k y P_k como puntos críticos para cada avión k
    vector<set<int>> pts(D);
    for (int k = 0; k < D; k++) {
        pts[k].insert(planes[k].E);
        pts[k].insert(planes[k].P);
    }

    // Paso 2: para cada par (j, k), el tiempo T_j + sep[j][k] es crítico para k.
    for (int j = 0; j < D; j++) {
        for (int k = 0; k < D; k++) {
            if (j == k) continue;
            int candidate = planes[j].E + sep[j][k];
            if (candidate >= planes[k].E && candidate <= planes[k].L)
                pts[k].insert(candidate);
            if (planes[j].E >= planes[k].E && planes[j].E <= planes[k].L)
                pts[k].insert(planes[j].E);
        }
    }

    // Último Paso: convertir sets a vectores ordenados
    domains.resize(D);
    for (int k = 0; k < D; k++)
        domains[k].assign(pts[k].begin(), pts[k].end());
}

void removeValue(int varIdx, int value, int trailLevel) {
    auto& dom = domains[varIdx];
    auto it   = find(dom.begin(), dom.end(), value);
    if (it != dom.end()) {
        dom.erase(it);
        trail[trailLevel].push_back({varIdx, value});
    }
}
void restoreDomains(int trailLevel) {
    for (auto& e : trail[trailLevel]) {
        auto& dom = domains[e.varIdx];
        dom.insert(lower_bound(dom.begin(), dom.end(), e.value), e.value);
    }
    trail[trailLevel].clear();
}


void printProgress() {
    double elapsed =
        duration_cast<milliseconds>(
            high_resolution_clock::now() - caseStartTime).count() / 1000.0;
    bool   hasSol  = (brisKet < 1e17);
    double optimum = hasSol ? brisKet : 0.0;
    double prevOpt = (prevBestCost < 1e17) ? prevBestCost : 0.0;

    cerr << "\r"
         << "  Nodos: "    << left  << setw(12) << nodesExplored
         << "  Ult_opt: "  << fixed << setprecision(2) << right << setw(12) << prevOpt
         << "  Optimo: "  << fixed << setprecision(2) << right << setw(12) << optimum
         << (hasSol ? "  " : "  (no sol)")
         << "  Tiempo: "     << setprecision(1) << setw(7) << elapsed << "s"
         << flush;
}

int selectVariable(const vector<bool>& assigned) {
    int best      = -1;
    int minDomain = INT_MAX;
    int bestDegree = -1;
    for (int i = 0; i < D; i++) {
        if (assigned[i]) continue;
        int domainSize = domains[i].size();
        int degree = 0;
        for (int j = 0; j < D; j++) {
            if (!assigned[j] && i != j && sep[i][j] > 0) degree++;
        }
        if (domainSize < minDomain) {
            minDomain  = domainSize;
            bestDegree = degree;
            best       = i;
        } else if (domainSize == minDomain && degree > bestDegree) {
            bestDegree = degree;
            best       = i;
        }
    }
    return best;
}

bool isConsistent(int future, int tf,
                  const vector<int>& assignment,
                  const vector<bool>& assigned)
{
    for (int j = 0; j < D; j++) {
        if (!assigned[j] || j == future) continue;
        int tj = assignment[j];
        if (tj <= tf && tf < tj + sep[j][future]) return false;
        if (tf <= tj && tj < tf + sep[future][j]) return false;
    }
    return true;
}

// Propagación MFC
bool minimalForwardCheck(int assignedIdx, int t,
                         const vector<int>& assignment,
                         const vector<bool>& assigned,
                         int trailLevel)
{
    for (int future = 0; future < D; future++) {
        if (assigned[future]) continue;
        auto& dom = domains[future];

        // Insertar punto crítico t + sep[assigned][future] si es válido y no está ya en el dominio
        {
            int newPt = t + sep[assignedIdx][future];
            if (newPt >= planes[future].E && newPt <= planes[future].L) {
                if (!binary_search(dom.begin(), dom.end(), newPt))
                    dom.insert(lower_bound(dom.begin(), dom.end(), newPt), newPt);
            }
        }
        // Caso 1: dominio singleton
        if (dom.size() == 1) {
            int tf = dom[0];
            bool incompat = false;
            if (t  <= tf && tf < t  + sep[assignedIdx][future]) incompat = true;
            if (tf <= t  && t  < tf + sep[future][assignedIdx]) incompat = true;
            if (!incompat) incompat = !isConsistent(future, tf, assignment, assigned);
            if (incompat) {
                removeValue(future, tf, trailLevel);
                return false;
            }
            continue;
        }
        // Caso 2: múltiples valores, eliminar los que son inconsistentes
        vector<int> toRemove;
        for (int tf : dom) {
            bool incompat = false;
            if (t  <= tf && tf < t  + sep[assignedIdx][future]) incompat = true;
            if (tf <= t  && t  < tf + sep[future][assignedIdx]) incompat = true;
            if (!incompat) incompat = !isConsistent(future, tf, assignment, assigned);
            if (incompat) toRemove.push_back(tf);
        }
        for (int val : toRemove) removeValue(future, val, trailLevel);

        if (dom.empty()) return false;
    }
    return true;
}

// Búsqueda MFC
void mfcSearch(vector<int>& assignment,
               vector<bool>& assigned,
               int level,
               double currentCost)
{
    nodesExplored++;
    if (timeoutFired.load(memory_order_acquire) ||
        userInterrupt.load(memory_order_acquire))
        throw TimeoutOptimum{};
    if (nodesExplored % PROGRESS_EVERY == 0) printProgress();

    if (level == D) {
        if (currentCost < brisKet) {
            prevBestCost   = brisKet;
            brisKet       = currentCost;
            bestAssignment = assignment;
            {
                lock_guard<mutex> lk(mtxLastOptimum);
                lastOptimumTime = high_resolution_clock::now();
            }
            printProgress();
        }
        return;
    }

    int idx = selectVariable(assigned);
    if (idx == -1) return;
    const Plane& av = planes[idx];
    // Heuristica de valor: Closest to Preferred Time
    vector<int> candidates = domains[idx];
    sort(candidates.begin(), candidates.end(), [&](int a, int b) {
        int da = abs(a - av.P), db = abs(b - av.P);
        if (da != db) return da < db;
        return computeCost(av, a) < computeCost(av, b);
    });

    for (int t : candidates) {
        double costT = computeCost(av, t);
        if (currentCost + costT >= brisKet) continue;

        assignment[idx] = t;
        assigned[idx]   = true;
        trail.push_back({});

        bool ok = minimalForwardCheck(idx, t, assignment, assigned,
                                      (int)trail.size() - 1);
        if (ok)
            mfcSearch(assignment, assigned, level + 1, currentCost + costT);

        restoreDomains((int)trail.size() - 1);
        trail.pop_back();
        assignment[idx] = -1;
        assigned[idx]   = false;
    }
}

bool readData(const string& filename) {
    ifstream fin(filename);
    if (!fin) { cerr << "\nError abriendo " << filename << "\n"; return false; }

    fin >> D;
    planes.resize(D);
    sep.assign(D, vector<int>(D));

    for (int i = 0; i < D; i++) {
        planes[i].id = i;
        fin >> planes[i].E >> planes[i].P >> planes[i].L
            >> planes[i].C >> planes[i].Cp;
        for (int j = 0; j < D; j++) fin >> sep[i][j];
        sep[i][i] = 0;
    }

    fin.close();
    return true;
}

void printSolution() {
    cout << fixed << setprecision(2);
    cout << "\n=== MFC  (MRV + Degree) ===\n";
    cout << "Nodos explorados : " << nodesExplored << "\n";
    cout << "Costo total      : " << brisKet      << "\n\n";

    cout << left
         << setw(6)  << "Avión"
         << setw(8)  << "E"
         << setw(8)  << "P"
         << setw(8)  << "L"
         << setw(10) << "T asign."
         << setw(10) << "Costo"  << "\n";
    cout << string(52, '-') << "\n";

    double total = 0;
    for (int i = 0; i < D; i++) {
        double c = computeCost(planes[i], bestAssignment[i]);
        total += c;
        cout << setw(6)  << i
             << setw(8)  << planes[i].E
             << setw(8)  << planes[i].P
             << setw(8)  << planes[i].L
             << setw(10) << bestAssignment[i]
             << setw(10) << c << "\n";
    }
    cout << string(52, '-') << "\n";
    cout << "Total cost: " << total << "\n";
}

//******************************************************************** MAIN
int main(int argc, char* argv[]) {
    if (argc < 3) {
        cerr << "Uso: ./mfc <pistas> <caso1> [caso2 ...]\n";
        return 1;
    }
    numRunways = stoi(argv[1]);

    for (int arg = 2; arg < argc; arg++) {
        string filename = argv[arg];
        cout << "\n=== Case: " << filename << " ===\n";

        brisKet = 1e18; prevBestCost = 1e18; nodesExplored = 0;
        planes.clear(); sep.clear();
        domains.clear(); trail.clear();
        bestAssignment.clear();

        if (!readData(filename)) {
            cout << "Error de lectura.\n"; continue;
        }
        initDomains();
        cout << "Aviones: " << D << " | Pistas: " << numRunways << "\n";
        cout << "Dominio discretizado (puntos criticos por avion):\n";
        for (int i = 0; i < D; i++)
            cout << "  Avion " << setw(2) << i
                 << ": " << setw(4) << domains[i].size() << " puntos"
                 << "  [" << domains[i].front()
                 << " .. " << domains[i].back() << "]\n";
        cout << "\n";

        vector<int>  assignment(D, -1);
        vector<bool> assigned(D, false);

        caseStartTime = high_resolution_clock::now();
        {
            lock_guard<mutex> lk(mtxLastOptimum);
            if (brisKet < 1e17)
                lastOptimumTime = high_resolution_clock::now();
            else
                lastOptimumTime = high_resolution_clock::now() + hours(24);
        }
        auto start = caseStartTime;
        cerr << "\n";

        // Verificar tiempo
        timeoutFired.store(false,    memory_order_relaxed);
        userInterrupt.store(false,   memory_order_relaxed);
        searchActive.store(true,     memory_order_relaxed);
        thread watchdog(watchdogThread);
        thread keyboard(keyboardThread);
        cerr << "  [Apretar 'q' para interrumpir y ver resultado actual]\n";

        bool byTimeout = false;
        bool byUser    = false;
        try {
            mfcSearch(assignment, assigned, 0, 0.0);
        } catch (const TimeoutOptimum&) {
            byUser    = userInterrupt.load(memory_order_acquire);
            byTimeout = !byUser;
            if (byUser)
                cerr << "\n[Interrumpido por usuario ('q')] Mostrando mejor solucion encontrada.\n";
            else
                cerr << "\n[Timeout] " << TIMEOUT_NO_OPTIMUM_SEC
                     << "s sin nuevo optimo — busqueda detenida.\n";
        } catch (...) {
            searchActive.store(false, memory_order_release);
            watchdog.join();
            keyboard.join();
            cerr << "\n";
            cout << "Error durante la ejecucion. Saltando.\n"; continue;
        }

        // Ve el teclado
        searchActive.store(false, memory_order_release);
        watchdog.join();
        keyboard.join();

        double ms = duration_cast<microseconds>(
            high_resolution_clock::now() - start).count() / 1000.0;
        cerr << "\n";

        cout << "Tiempo de ejecucion: " << ms << " ms";
        if (byTimeout) cout << "  [detenido por timeout: " << TIMEOUT_NO_OPTIMUM_SEC << "s sin nuevo optimo]";
        if (byUser)    cout << "  [interrumpido por usuario]";
        cout << "\n";
        if (brisKet < 1e17) printSolution();
        else cout << "No se encontro solucion factible.\n";
    }
    return 0;
}
