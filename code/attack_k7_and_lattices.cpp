#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <omp.h>
#include <random>
#include <set>
#include <string>
#include <vector>

using namespace std;

// Exact E_8 enumeration for small L to verify Theta_{E_8} = 1 + 240 * sum sigma_3(m) q^{2m}
// E_8 = {x in Z^8 u (Z + 1/2)^8 : sum x_i in 2Z}. In doubled coordinates y = 2x in Z^8:
// all y_i same parity, sum y_i == 0 (mod 4), and ||y||^2 = 4 * ||x||^2 = 8 * m.
static vector<uint64_t> e8_shell_counts_bruteforce(int max_m) {
    vector<uint64_t> counts(max_m + 1, 0);
    int64_t max_sq = 8LL * max_m;
    int maxv = (int)floor(sqrt((double)max_sq));
    // DP for each parity par in {0, 1}: state (sum mod 4, normSq)
    for (int par = 0; par <= 1; ++par) {
        vector<vector<uint64_t>> dp(4, vector<uint64_t>(max_sq + 1, 0));
        dp[0][0] = 1;
        for (int dim = 0; dim < 8; ++dim) {
            vector<vector<uint64_t>> ndp(4, vector<uint64_t>(max_sq + 1, 0));
            for (int v = -maxv; v <= maxv; ++v) {
                if ((abs(v) & 1) != par) continue;
                int64_t sq = (int64_t)v * v;
                int rem4 = ((v % 4) + 4) % 4;
                for (int r = 0; r < 4; ++r) {
                    int nr = (r + rem4) & 3;
                    for (int64_t s = 0; s + sq <= max_sq; ++s) {
                        ndp[nr][s + sq] += dp[r][s];
                    }
                }
            }
            dp = move(ndp);
        }
        for (int m = 0; m <= max_m; ++m) counts[m] += dp[0][8 * m];
    }
    return counts;
}

static uint64_t sigma3(uint64_t m) {
    uint64_t s = 0;
    for (uint64_t d = 1; d * d <= m; ++d) {
        if (m % d == 0) {
            s += d * d * d;
            uint64_t o = m / d;
            if (o != d) s += o * o * o;
        }
    }
    return s;
}

// Also compute Leech lattice Theta_{Lambda_24}(q) = E_4(q)^3 - 720 * Delta(q) up to m <= 30
// Delta(q) = sum_{n>=1} tau(n) q^{2n} where coefficients are exact int64
// Wait: q^{2n} is degree n in q^2. Let F(t) = 1 + 240 * sum_{m>=1} sigma_3(m) t^m (t = q^2).
// And Delta(t) = t * prod_{k>=1} (1 - t^k)^24!
static void test_lattices() {
    cout << "=== 1. Verifying E_8 Theta Series vs Exact DP ===" << endl;
    auto dp_e8 = e8_shell_counts_bruteforce(8);
    for (int m = 0; m <= 8; ++m) {
        uint64_t th = (m == 0) ? 1ULL : (240ULL * sigma3(m));
        cout << "  E_8 shell 2m=" << 2*m << ": dp=" << dp_e8[m] << " theorem=" << th << endl;
    }

    cout << "\n=== 2. E_8 Crossover vs D_8 and Quadratic k^2+3k-11 ===" << endl;
    // E_8: union_{i=0}^{L-1} 2^i (B_{2(L-i)}(c) cap E_8) u {2^L c}, k <= L * 2^8 + 1 = 256*L + 1
    uint64_t prefE8 = 0, ballE8 = 0;
    for (int L = 1; L <= 40; ++L) {
        ballE8 += (L == 0 ? 1ULL : 240ULL * sigma3(L));
        // Wait: B_{2(L)} includes normSq < 2(L) or <= 2(L): let's use strictly < 2*m or <= 2*(m-1)?
        // Consistent with ruzsa_lattice_test.cpp: |B_{2L}| includes normSq <= 2L (or < 2L -> step 2).
        // Let's check: in ruzsa_lattice_test.cpp, cntD[2*L] = sum_{r <= 2L} shell_r, and we require B_{2(L-i)} with closed ball <= 2(L-i)?
        // Wait: if u,v have ||u-c||^2 <= 2m and ||v-c||^2 <= 2m, u != v same coset mod 2D_d:
        // ||(u+v)/2 - c||^2 <= 2m - 2 = 2(m-1)! And at i=L-1, m=1, ||(u+v)/2 - c||^2 <= 0 => = c in B_0(c) = {c}!
        // Note for u != v in E_8 with ||u-c||^2 <= 2m, ||v-c||^2 <= 2m and u-v in 2E_8 \ {0}:
        // ||(u-v)/2||^2 >= 2 (since E_8 has min norm^2 = 2), so ||(u+v)/2 - c||^2 <= 2(m-1) EXACTLY!
    }
    // Recompute cleanly: ball_E8[m] = sum_{j=0}^m shell[j], where shell[0]=1, shell[j]=240*sigma3(j).
    uint64_t bE8 = 1, cumE8 = 0;
    for (int L = 1; L <= 30; ++L) {
        bE8 += 240ULL * sigma3(L);
        cumE8 += bE8;
        uint64_t n = cumE8 + 1;
        uint64_t k = (uint64_t)L * 256ULL + 1ULL;
        uint64_t quad = k * k + 3 * k - 11;
        if (n > quad) {
            cout << "  [E_8 FIRST BEATS k^2+3k-11] L=" << L << " k<=" << k
                 << " n=" << n << " (quad=" << quad << ")" << endl;
            break;
        }
    }

    // Leech lattice Lambda_24: exact shell counts up to m=20 using __int128
    // t = q^2: E4(t) = 1 + 240*sum sigma3(m) t^m. Delta(t) = t * prod_{k=1}^{M} (1 - t^k)^24 mod t^{M+1}
    int M = 25;
    vector<__int128> E4(M + 1, 0), Delta(M + 1, 0), P(M + 1, 0);
    E4[0] = 1;
    for (int m = 1; m <= M; ++m) E4[m] = (__int128)240 * sigma3(m);
    // Multiply E4^3
    vector<__int128> E4_2(M + 1, 0), E4_3(M + 1, 0);
    for (int a = 0; a <= M; ++a)
        for (int b = 0; a + b <= M; ++b)
            E4_2[a + b] += E4[a] * E4[b];
    for (int a = 0; a <= M; ++a)
        for (int b = 0; a + b <= M; ++b)
            E4_3[a + b] += E4_2[a] * E4[b];
    P[0] = 1;
    for (int k = 1; k <= M; ++k) {
        // Multiply by (1 - t^k)^24 via 24 steps of (1 - t^k)
        for (int rep = 0; rep < 24; ++rep) {
            for (int j = M; j >= k; --j) P[j] -= P[j - k];
        }
    }
    for (int m = 1; m <= M; ++m) Delta[m] = P[m - 1];
    vector<__int128> L24_shell(M + 1, 0);
    for (int m = 0; m <= M; ++m) L24_shell[m] = E4_3[m] - (__int128)720 * Delta[m];
    cout << "  Leech shell check: L[0]=" << (int64_t)L24_shell[0]
         << " L[1]=" << (int64_t)L24_shell[1]
         << " L[2]=" << (int64_t)L24_shell[2]
         << " L[3]=" << (int64_t)L24_shell[3] << endl;
    // Note for Leech: normSq step is 2 (shells are 2m), AND min nonzero normSq is 4!
    // So any same-coset pair in B_{4L} drops by >= 4 into B_{4(L-1)}!
    // Wait: if we step in B_{4L} = {normSq <= 4L}, wait between B_{4L} and B_{4(L-1)},
    // shell 4L has index m = 2L.
    // Let's compare k <= L * 2^24 vs |A| = sum_{j=1}^L |B_{4j}|:
    __int128 bL24 = L24_shell[0] + L24_shell[1]; // m=0..1 (normSq=0)
    __int128 cumL24 = 0;
    for (int L = 1; 2 * L <= M; ++L) {
        bL24 += L24_shell[2 * L - 1] + L24_shell[2 * L];
        cumL24 += bL24;
        if (L == 3 || L == 6 || L == 10 || L == 12) {
            unsigned __int128 n = (unsigned __int128)(cumL24 + 1);
            unsigned __int128 k = (unsigned __int128)L * (1ULL << 24) + 1;
            unsigned __int128 q = k * k + 3 * k - 11;
            double ratio = (double)n / (double)q;
            cout << "  [Leech_24] L=" << L << " n/quad_bound=" << fixed << setprecision(3) << ratio << endl;
        }
    }
}

// Fast 128-bit graph engine
static constexpr int MAX_N = 128;
static inline int ctz128(__uint128_t x) {
    uint64_t lo = (uint64_t)x;
    if (lo) return __builtin_ctzll(lo);
    return 64 + __builtin_ctzll((uint64_t)(x >> 64));
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
    int n = 0; int64_t elements[MAX_N];
    __uint128_t adj_G[MAX_N], comp_adj[MAX_N];
    int best_alpha = 0, target_stop = 0; __uint128_t best_mask = 0;
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
        for (int i = 0; i < n; ++i) { elements[i] = A[ord[i]]; adj_G[i] = 0; comp_adj[i] = 0; }
        for (int i = 0; i < n; ++i) {
            int64_t u = elements[i];
            for (int j = i + 1; j < n; ++j) {
                if (sA.contains(u + elements[j])) { adj_G[i] |= bit128(j); adj_G[j] |= bit128(i); }
                else { comp_adj[i] |= bit128(j); comp_adj[j] |= bit128(i); }
            }
        }
    }
    inline __uint128_t full_mask() const { return (n == 128) ? (~(__uint128_t)0) : (bit128(n) - 1); }
    void expand(__uint128_t P, int depth, __uint128_t cur_mask) {
        if (!P) { if (depth > best_alpha) { best_alpha = depth; best_mask = cur_mask; } return; }
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
            if (next_P) expand(next_P, depth + 1, cur_mask | bit128(v));
            else if (depth + 1 > best_alpha) { best_alpha = depth + 1; best_mask = cur_mask | bit128(v); }
            if (target_stop > 0 && best_alpha >= target_stop) return;
        }
    }
    int exact_alpha() { best_alpha = 0; target_stop = 0; expand(full_mask(), 0, 0); return best_alpha; }
    void count_k_rec(__uint128_t P, int depth, int target_k, uint64_t& count, uint64_t cap,
                     __uint128_t cur_mask, vector<__uint128_t>* samples, int max_samples) {
        int need = target_k - depth;
        if (popcnt128(P) < need) return;
        if (need == 1) {
            int sz = popcnt128(P);
            if (samples && (int)samples->size() < max_samples) {
                __uint128_t tmp = P;
                while (tmp && (int)samples->size() < max_samples) {
                    int v = ctz128(tmp); samples->push_back(cur_mask | bit128(v)); tmp ^= bit128(v);
                }
            }
            count += (uint64_t)sz; return;
        }
        if (need == 2) {
            __uint128_t rem = P;
            while (rem) {
                int v = ctz128(rem); rem ^= bit128(v);
                __uint128_t nb = rem & comp_adj[v]; int c2 = popcnt128(nb);
                if (c2 > 0) {
                    if (samples && (int)samples->size() < max_samples) {
                        __uint128_t t = nb;
                        while (t && (int)samples->size() < max_samples) {
                            int w = ctz128(t); samples->push_back(cur_mask | bit128(v) | bit128(w)); t ^= bit128(w);
                        }
                    }
                    count += (uint64_t)c2; if (count >= cap) return;
                }
            }
            return;
        }
        int order[MAX_N], color[MAX_N], m = 0, c = 0; __uint128_t U = P;
        while (U) {
            c++; __uint128_t Q = U;
            while (Q) { int v = ctz128(Q); order[m] = v; color[m] = c; m++; U ^= bit128(v); Q &= adj_G[v]; }
        }
        if (c < need) return;
        for (int i = m - 1; i >= 0; --i) {
            if (color[i] < need) return;
            int v = order[i]; P ^= bit128(v);
            __uint128_t next_P = P & comp_adj[v];
            if (popcnt128(next_P) >= need - 1) {
                count_k_rec(next_P, depth + 1, target_k, count, cap, cur_mask | bit128(v), samples, max_samples);
                if (count >= cap) return;
            }
        }
    }
    uint64_t count_indep(int target_k, uint64_t cap = UINT64_MAX, vector<__uint128_t>* samples = nullptr, int max_samples = 0) {
        if (samples) samples->clear();
        uint64_t count = 0;
        count_k_rec(full_mask(), 0, target_k, count, cap, 0, samples, max_samples);
        return min(count, cap);
    }
};

static vector<int64_t> make_doubled(const vector<int64_t>& A, int k_new) {
    vector<int64_t> out;
    for (int64_t x : A) out.push_back(2 * x);
    for (int j = 0; j <= k_new; ++j) { out.push_back(-(2 * j + 1)); out.push_back(2 * j + 1); }
    sort(out.begin(), out.end()); out.erase(unique(out.begin(), out.end()), out.end());
    return out;
}

static void deep_sa(int n, int target_alpha, int mode, int64_t U, double seconds,
                    const vector<int64_t>& seed, const string& tag) {
    int g_best_alpha = 999999; uint64_t g_best_cnt = UINT64_MAX;
    vector<int64_t> g_best_A; bool g_found = false;
    auto t0 = chrono::steady_clock::now();

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        mt19937_64 rng(0x123456789abcdef1ULL + (uint64_t)tid * 999983ULL + (uint64_t)n);
        uniform_real_distribution<double> u01(0.0, 1.0);
        TinySet sA; Graph128 g;

        auto to_full = [&](const vector<int64_t>& st) {
            if (mode != 2) return st;
            vector<int64_t> full;
            for (int i = (int)st.size() - 1; i >= 0; --i) full.push_back(-st[i]);
            full.push_back(0);
            for (int64_t x : st) full.push_back(x);
            return full;
        };

        auto eval_s = [&](const vector<int64_t>& st, int& oa, uint64_t& oc,
                          vector<__uint128_t>& samps, vector<int64_t>& full, vector<int64_t>& hot) {
            full = to_full(st);
            g.build(full, sA);
            oa = g.exact_alpha();
            oc = g.count_indep(oa, 20000, &samps, 128);
            hot.clear();
            map<int64_t, int> freq;
            int lim = min((int)samps.size(), 64);
            for (int s = 0; s < lim; ++s) {
                vector<int64_t> vec; __uint128_t m = samps[s];
                while (m) { int v = ctz128(m); m ^= bit128(v); vec.push_back(g.elements[v]); }
                for (size_t a = 0; a < vec.size(); ++a) for (size_t b = a + 1; b < vec.size(); ++b) {
                    int64_t sm = vec[a] + vec[b];
                    int64_t key = (mode == 2) ? llabs(sm) : sm;
                    if (mode == 1 && (key < 1 || key > U)) continue;
                    if (mode == 2 && (key < 1 || key > U)) continue;
                    if (mode == 0 && (key < -U || key > U)) continue;
                    if (!sA.contains(sm)) freq[key]++;
                }
            }
            vector<pair<int, int64_t>> rk;
            for (auto& kv : freq) rk.push_back({kv.second, kv.first});
            sort(rk.rbegin(), rk.rend());
            for (int q = 0; q < min((int)rk.size(), 12); ++q) hot.push_back(rk[q].second);
        };

        int state_sz = (mode == 2) ? ((n - 1) / 2) : n;
        int restart = 0;
        while (chrono::duration<double>(chrono::steady_clock::now() - t0).count() < seconds) {
            bool f;
            #pragma omp atomic read
            f = g_found; if (f) break;

            vector<int64_t> cur;
            for (int64_t x : seed) {
                if (mode == 0 && x >= -U && x <= U) cur.push_back(x);
                if (mode == 1 && x >= 1 && x <= U) cur.push_back(x);
                if (mode == 2 && x >= 1 && x <= U) cur.push_back(x);
            }
            sort(cur.begin(), cur.end()); cur.erase(unique(cur.begin(), cur.end()), cur.end());
            while ((int)cur.size() > state_sz) cur.erase(cur.begin() + (rng() % cur.size()));
            while ((int)cur.size() < state_sz) {
                int64_t cand = (mode == 0) ? (-U + (int64_t)(rng() % (2 * U + 1))) : (1 + (int64_t)(rng() % U));
                if (find(cur.begin(), cur.end(), cand) == cur.end()) cur.push_back(cand);
            }
            if (restart > 0) {
                int ks = 1 + (restart % 4);
                for (int q = 0; q < ks; ++q) {
                    int idx = rng() % state_sz;
                    int64_t cand = (mode == 0) ? (-U + (int64_t)(rng() % (2 * U + 1))) : (1 + (int64_t)(rng() % U));
                    if (find(cur.begin(), cur.end(), cand) == cur.end()) cur[idx] = cand;
                }
            }
            sort(cur.begin(), cur.end()); restart++;

            int ca = 999999; uint64_t cc = UINT64_MAX;
            vector<__uint128_t> cs; vector<int64_t> cf, ch;
            eval_s(cur, ca, cc, cs, cf, ch);
            #pragma omp critical
            {
                if (ca < g_best_alpha || (ca == g_best_alpha && cc < g_best_cnt)) {
                    g_best_alpha = ca; g_best_cnt = cc; g_best_A = cf;
                    if (ca <= target_alpha) g_found = true;
                }
            }

            int no_imp = 0;
            for (int it = 0; it < 60000 && no_imp < 4000; ++it) {
                if ((it & 63) == 0 && chrono::duration<double>(chrono::steady_clock::now() - t0).count() >= seconds) break;
                bool f2;
                #pragma omp atomic read
                f2 = g_found; if (f2) break;

                vector<int64_t> nxt = cur;
                bool moved = false;
                if (u01(rng) < 0.72 && !ch.empty()) {
                    int64_t av = ch[rng() % min((int)ch.size(), 4)];
                    if (find(nxt.begin(), nxt.end(), av) == nxt.end()) {
                        int ri = rng() % state_sz;
                        if (!cs.empty() && u01(rng) < 0.55) {
                            __uint128_t sm = cs[rng() % cs.size()];
                            vector<int64_t> vs;
                            while (sm) {
                                int v = ctz128(sm); sm ^= bit128(v);
                                int64_t xv = (mode == 2) ? llabs(g.elements[v]) : g.elements[v];
                                if (mode == 2 && xv == 0) continue;
                                vs.push_back(xv);
                            }
                            if (!vs.empty()) {
                                int64_t pv = vs[rng() % vs.size()];
                                for (int i = 0; i < state_sz; ++i) if (nxt[i] == pv) { ri = i; break; }
                            }
                        }
                        nxt[ri] = av; moved = true;
                    }
                }
                if (!moved) {
                    int ri = rng() % state_sz;
                    int64_t cand = (u01(rng) < 0.5) ? (nxt[ri] + (1 + (rng() % 4)) * ((rng() & 1) ? 1 : -1))
                                                     : ((mode == 0) ? (-U + (int64_t)(rng() % (2 * U + 1))) : (1 + (int64_t)(rng() % U)));
                    bool ok = (mode == 0) ? (cand >= -U && cand <= U) : (cand >= 1 && cand <= U);
                    if (ok && find(nxt.begin(), nxt.end(), cand) == nxt.end()) { nxt[ri] = cand; moved = true; }
                }
                if (!moved) continue;
                sort(nxt.begin(), nxt.end());

                int na = 999999; uint64_t nc = UINT64_MAX;
                vector<__uint128_t> ns; vector<int64_t> nf, nh;
                eval_s(nxt, na, nc, ns, nf, nh);

                bool acc = (na < ca) || (na == ca && nc <= cc) ||
                           (na == ca && u01(rng) < 0.1 * exp(-(double)(nc - cc) / max(1.0, 0.15 * cc)));
                if (acc) {
                    if (na < ca || (na == ca && nc < cc)) no_imp = 0; else no_imp++;
                    cur = move(nxt); ca = na; cc = nc; cs = move(ns); cf = move(nf); ch = move(nh);
                    if (ca < g_best_alpha || (ca == g_best_alpha && cc < g_best_cnt)) {
                        #pragma omp critical
                        {
                            if (ca < g_best_alpha || (ca == g_best_alpha && cc < g_best_cnt)) {
                                g_best_alpha = ca; g_best_cnt = cc; g_best_A = cf;
                                if (ca <= target_alpha) g_found = true;
                            }
                        }
                    }
                } else no_imp++;
            }
        }
    }
    cout << "[" << tag << "] n=" << n << " target=" << target_alpha << " mode=" << mode
         << " U=" << U << " -> best_alpha=" << g_best_alpha << " cnt=" << g_best_cnt << endl;
    if (g_best_alpha <= target_alpha) {
        cout << "  *** TARGET HIT! SET:";
        for (int64_t x : g_best_A) cout << " " << x;
        cout << endl;
    }
}

int main() {
    test_lattices();
    vector<int64_t> A43 = {-42,-26,-24,-22,-20,-18,-16,-14,-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,
                           1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,18,20,22,24,26,42};
    auto A59 = make_doubled(A43, 7);
    auto A59_m17 = A59; A59_m17.push_back(-17); sort(A59_m17.begin(), A59_m17.end());
    vector<int64_t> P29; for (int64_t x : A59) if (x > 0) P29.push_back(x);
    auto P30 = P29; P30.push_back(17);

    cout << "\n=== 3. Targeted Deep Local SA Around Optimal Seeds ===" << endl;
    deep_sa(30, 7, 1, 140, 5.0, P30, "POS_m30_from_P29");
    deep_sa(60, 7, 0, 120, 6.0, A59_m17, "FREE_n60_from_A59_m17");
    auto A77 = make_doubled(A59, 8);
    auto A77_m19 = A77; A77_m19.push_back(-19); sort(A77_m19.begin(), A77_m19.end());
    deep_sa(78, 8, 0, 220, 6.0, A77_m19, "FREE_n78_from_A77_m19");
    return 0;
}
