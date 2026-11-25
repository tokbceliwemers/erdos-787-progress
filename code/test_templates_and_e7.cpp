#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <omp.h>
#include <vector>

using namespace std;

static constexpr int MAX_N = 128;
static inline int ctz128(__uint128_t x) {
    uint64_t lo = (uint64_t)x;
    return lo ? __builtin_ctzll(lo) : (64 + __builtin_ctzll((uint64_t)(x >> 64)));
}
static inline int popcnt128(__uint128_t x) {
    return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64));
}
static inline __uint128_t bit128(int i) { return ((__uint128_t)1) << i; }

struct TinySet {
    static constexpr int CAP = 1024;
    int64_t keys[CAP]; uint32_t gens[CAP]; uint32_t cur_gen = 1;
    TinySet() { memset(gens, 0, sizeof(gens)); }
    inline void clear() { cur_gen++; if (cur_gen == 0) { memset(gens, 0, sizeof(gens)); cur_gen = 1; } }
    static inline uint32_t hash64(int64_t x) {
        uint64_t h = (uint64_t)x * 0x9e3779b97f4a7c15ULL; h ^= h >> 30; h *= 0xbf58476d1ce4e5b9ULL; h ^= h >> 27;
        return (uint32_t)(h & (CAP - 1));
    }
    inline void insert(int64_t x) {
        uint32_t idx = hash64(x);
        while (gens[idx] == cur_gen) { if (keys[idx] == x) return; idx = (idx + 1) & (CAP - 1); }
        keys[idx] = x; gens[idx] = cur_gen;
    }
    inline bool contains(int64_t x) const {
        uint32_t idx = hash64(x);
        while (gens[idx] == cur_gen) { if (keys[idx] == x) return true; idx = (idx + 1) & (CAP - 1); }
        return false;
    }
};

struct Graph128 {
    int n = 0;
    __uint128_t adj_G[MAX_N], comp_adj[MAX_N];
    int best_alpha = 0, target_stop = 0;

    void build(const vector<int64_t>& A, TinySet& sA) {
        n = (int)A.size(); sA.clear(); for (int i = 0; i < n; ++i) sA.insert(A[i]);
        int raw_deg[MAX_N] = {};
        for (int i = 0; i < n; ++i) for (int j = i + 1; j < n; ++j)
            if (sA.contains(A[i] + A[j])) { raw_deg[i]++; raw_deg[j]++; }
        int ord[MAX_N]; for (int i = 0; i < n; ++i) ord[i] = i;
        sort(ord, ord + n, [&](int a, int b) {
            if (raw_deg[a] != raw_deg[b]) return raw_deg[a] < raw_deg[b];
            return A[a] < A[b];
        });
        int64_t el[MAX_N];
        for (int i = 0; i < n; ++i) { el[i] = A[ord[i]]; adj_G[i] = 0; comp_adj[i] = 0; }
        for (int i = 0; i < n; ++i) for (int j = i + 1; j < n; ++j) {
            if (sA.contains(el[i] + el[j])) { adj_G[i] |= bit128(j); adj_G[j] |= bit128(i); }
            else { comp_adj[i] |= bit128(j); comp_adj[j] |= bit128(i); }
        }
    }
    inline __uint128_t full_mask() const { return (n == 128) ? (~(__uint128_t)0) : (bit128(n) - 1); }
    void expand(__uint128_t P, int depth) {
        if (!P) { if (depth > best_alpha) best_alpha = depth; return; }
        if (depth + popcnt128(P) <= best_alpha) return;
        int order[MAX_N], color[MAX_N], m = 0, c = 0; __uint128_t U = P;
        while (U) {
            c++; __uint128_t Q = U;
            while (Q) { int v = ctz128(Q); order[m] = v; color[m] = c; m++; U ^= bit128(v); Q &= adj_G[v]; }
        }
        if (depth + c <= best_alpha) return;
        for (int i = m - 1; i >= 0; --i) {
            if (depth + color[i] <= best_alpha) return;
            int v = order[i]; P ^= bit128(v);
            __uint128_t next_P = P & comp_adj[v];
            if (next_P) expand(next_P, depth + 1);
            else if (depth + 1 > best_alpha) best_alpha = depth + 1;
            if (target_stop > 0 && best_alpha >= target_stop) return;
        }
    }
    bool has_indep_ge(int k) {
        best_alpha = k - 1; target_stop = k;
        expand(full_mask(), 0);
        return best_alpha >= k;
    }
    int exact_alpha() {
        best_alpha = 0; target_stop = 0;
        expand(full_mask(), 0);
        return best_alpha;
    }
};

static vector<int64_t> sym_from_pos(const vector<int64_t>& P) {
    vector<int64_t> A;
    A.reserve(2 * P.size() + 1);
    for (int i = (int)P.size() - 1; i >= 0; --i) A.push_back(-P[i]);
    A.push_back(0);
    for (int64_t x : P) A.push_back(x);
    return A;
}

// Compute D_d crossover with tight bound k <= (L-1)*2^d + d(d-1) + 2
static void check_dd_tight() {
    cout << "=== 1. Tight D_d Crossover with Top-Shell Exact Bound k <= (L-1)*2^d + d*(d-1) + 2 ===" << endl;
    for (int d : {3, 4, 5, 6, 7, 8}) {
        int max_r = (d <= 4 ? 400 : 120);
        vector<vector<uint64_t>> dp(2, vector<uint64_t>(max_r + 1, 0));
        dp[0][0] = 1;
        int maxv = (int)floor(sqrt((double)max_r));
        for (int dim = 0; dim < d; ++dim) {
            vector<vector<uint64_t>> ndp(2, vector<uint64_t>(max_r + 1, 0));
            for (int v = -maxv; v <= maxv; ++v) {
                int sq = v * v, par = abs(v) & 1;
                for (int p = 0; p < 2; ++p)
                    for (int r = 0; r + sq <= max_r; ++r)
                        ndp[p ^ par][r + sq] += dp[p][r];
            }
            dp = move(ndp);
        }
        vector<uint64_t> ball(max_r + 1, 0);
        uint64_t run = 0;
        for (int r = 0; r <= max_r; ++r) { run += dp[0][r]; ball[r] = run; }

        uint64_t cum = 0;
        for (int L = 1; 2 * L <= max_r; ++L) {
            cum += ball[2 * L];
            uint64_t n = cum + 1;
            uint64_t k = (uint64_t)(L - 1) * (1ULL << d) + (uint64_t)d * (d - 1) + 2;
            uint64_t quad = k * k + 3 * k - 11;
            if (n > quad) {
                cout << "  D_" << d << " TIGHT FIRST CROSS: L=" << L << " k<=" << k
                     << " n=" << n << " (quad=" << quad << ")" << endl;
                break;
            }
        }
    }
}

int main() {
    check_dd_tight();

    // 2. Search 2-tier symmetric templates P = [1..B] u {B+2..E} u {T} and 3-tier + gap variants for k=6,7,8
    cout << "\n=== 2. Exhaustive Multi-Tier Template Search for P_{30} (k=7) and A_{60} ===" << endl;
    int best_m7 = 0;
    vector<int64_t> best_P7;
    #pragma omp parallel
    {
        TinySet sA; Graph128 g;
        int lbest = 0; vector<int64_t> lP;
        #pragma omp for schedule(dynamic, 1)
        for (int B = 10; B <= 26; ++B) {
            for (int E = B; E <= 44; E += 2) {
                for (int T = E + 2; T <= 2 * E; ++T) {
                    vector<int64_t> P;
                    for (int x = 1; x <= B; ++x) P.push_back(x);
                    for (int x = B + 2; x <= E; x += 2) P.push_back(x);
                    P.push_back(T);
                    if ((int)P.size() < 29 || (int)P.size() > 38) continue;
                    g.build(P, sA);
                    if (!g.has_indep_ge(8)) {
                        auto S = sym_from_pos(P);
                        g.build(S, sA);
                        int aS = g.exact_alpha();
                        if (aS <= 7 && (int)P.size() > lbest) {
                            lbest = (int)P.size();
                            lP = P;
                        }
                    }
                }
            }
        }
        #pragma omp critical
        {
            if (lbest > best_m7) { best_m7 = lbest; best_P7 = lP; }
        }
    }
    cout << "Best 2-tier [1..B] u evens(B+2..E) u {T} with alpha(S)<=7: m_+=" << best_m7
         << " (|S|=" << (best_m7 > 0 ? 2*best_m7+1 : 0) << ")" << endl;
    if (!best_P7.empty()) {
        cout << "  P=";
        for (int64_t x : best_P7) cout << " " << x;
        cout << endl;
    }

    // 3. Search 3-tier [1..B] u evens(B+2..E1) u step4(E1+4..E2) u {T1..} centered near A59_+
    cout << "\n=== 3. Exhaustive 3-tier [1..B] u step2(E1) u step4(E2) u {T} around k=7 ===" << endl;
    int best3 = 0; vector<int64_t> best3P;
    #pragma omp parallel
    {
        TinySet sA; Graph128 g;
        int lbest = 0; vector<int64_t> lP;
        #pragma omp for schedule(dynamic, 1)
        for (int B = 12; B <= 22; ++B) {
            for (int E1 = B; E1 <= 34; E1 += 2) {
                for (int E2 = E1; E2 <= 64; E2 += 4) {
                    int base_sz = B + (E1 - B) / 2 + (E2 - E1) / 4;
                    if (base_sz + 1 < 29 || base_sz + 1 > 34) continue;
                    for (int T = E2 + 2; T <= 2 * E2; T += 2) {
                        vector<int64_t> P;
                        for (int x = 1; x <= B; ++x) P.push_back(x);
                        for (int x = B + 2; x <= E1; x += 2) P.push_back(x);
                        for (int x = E1 + 4; x <= E2; x += 4) P.push_back(x);
                        P.push_back(T);
                        g.build(P, sA);
                        if (!g.has_indep_ge(8)) {
                            auto S = sym_from_pos(P);
                            g.build(S, sA);
                            if (!g.has_indep_ge(8) && (int)P.size() > lbest) {
                                lbest = (int)P.size(); lP = P;
                            }
                        }
                    }
                }
            }
        }
        #pragma omp critical
        {
            if (lbest > best3) { best3 = lbest; best3P = lP; }
        }
    }
    cout << "Best 3-tier with alpha(S)<=7: m_+=" << best3 << " (|S|=" << (best3 > 0 ? 2*best3+1 : 0) << ")" << endl;
    if (!best3P.empty()) {
        cout << "  P=";
        for (int64_t x : best3P) cout << " " << x;
        cout << endl;
    }

    return 0;
}
