#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <omp.h>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace std;

static constexpr int MAX_N = 128;

static inline int ctz128(__uint128_t x) {
    uint64_t lo = (uint64_t)x;
    if (lo) return __builtin_ctzll(lo);
    return 64 + __builtin_ctzll((uint64_t)(x >> 64));
}

static inline int popcnt128(__uint128_t x) {
    return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64));
}

static inline __uint128_t bit128(int i) {
    return ((__uint128_t)1) << i;
}

struct TinySet {
    static constexpr int CAP = 1024;
    int64_t keys[CAP];
    uint32_t gens[CAP];
    uint32_t cur_gen = 1;

    TinySet() { memset(gens, 0, sizeof(gens)); }

    inline void clear() {
        cur_gen++;
        if (cur_gen == 0) {
            memset(gens, 0, sizeof(gens));
            cur_gen = 1;
        }
    }

    static inline uint32_t hash64(int64_t x) {
        uint64_t h = (uint64_t)x * 0x9e3779b97f4a7c15ULL;
        h ^= h >> 30;
        h *= 0xbf58476d1ce4e5b9ULL;
        h ^= h >> 27;
        return (uint32_t)(h & (CAP - 1));
    }

    inline void insert(int64_t x) {
        uint32_t idx = hash64(x);
        while (gens[idx] == cur_gen) {
            if (keys[idx] == x) return;
            idx = (idx + 1) & (CAP - 1);
        }
        keys[idx] = x;
        gens[idx] = cur_gen;
    }

    inline bool contains(int64_t x) const {
        uint32_t idx = hash64(x);
        while (gens[idx] == cur_gen) {
            if (keys[idx] == x) return true;
            idx = (idx + 1) & (CAP - 1);
        }
        return false;
    }
};

struct Graph128 {
    int n = 0;
    int64_t orig_elements[MAX_N];
    int perm_to_orig[MAX_N];
    int64_t elements[MAX_N];
    __uint128_t adj_G[MAX_N];
    __uint128_t comp_adj[MAX_N];
    int deg_G[MAX_N];
    int edges_G = 0;

    int best_alpha = 0;
    __uint128_t best_mask = 0;
    int target_stop = 0;
    uint64_t nodes_visited = 0;

    void build(const vector<int64_t>& A, TinySet& sA, int order_mode = 2) {
        n = (int)A.size();
        sA.clear();
        for (int i = 0; i < n; ++i) {
            orig_elements[i] = A[i];
            sA.insert(A[i]);
        }

        int raw_deg[MAX_N];
        memset(raw_deg, 0, sizeof(int) * n);
        edges_G = 0;
        for (int i = 0; i < n; ++i) {
            int64_t u = orig_elements[i];
            for (int j = i + 1; j < n; ++j) {
                if (sA.contains(u + orig_elements[j])) {
                    raw_deg[i]++;
                    raw_deg[j]++;
                    edges_G++;
                }
            }
        }

        int ord[MAX_N];
        for (int i = 0; i < n; ++i) ord[i] = i;
        if (order_mode == 1) {
            sort(ord, ord + n, [&](int a, int b) {
                if (raw_deg[a] != raw_deg[b]) return raw_deg[a] > raw_deg[b];
                return orig_elements[a] < orig_elements[b];
            });
        } else if (order_mode == 2) {
            // Ascending deg_G = descending deg_Gbar: fastest BBMC ordering
            sort(ord, ord + n, [&](int a, int b) {
                if (raw_deg[a] != raw_deg[b]) return raw_deg[a] < raw_deg[b];
                return orig_elements[a] < orig_elements[b];
            });
        }

        for (int i = 0; i < n; ++i) {
            perm_to_orig[i] = ord[i];
            elements[i] = orig_elements[ord[i]];
            adj_G[i] = 0;
            comp_adj[i] = 0;
            deg_G[i] = raw_deg[ord[i]];
        }

        for (int i = 0; i < n; ++i) {
            int64_t u = elements[i];
            for (int j = i + 1; j < n; ++j) {
                if (sA.contains(u + elements[j])) {
                    adj_G[i] |= bit128(j);
                    adj_G[j] |= bit128(i);
                } else {
                    comp_adj[i] |= bit128(j);
                    comp_adj[j] |= bit128(i);
                }
            }
        }
    }

    inline __uint128_t full_mask() const {
        return (n == 128) ? (~(__uint128_t)0) : (bit128(n) - 1);
    }

    void expand(__uint128_t P, int depth, __uint128_t cur_mask) {
        nodes_visited++;
        if (!P) {
            if (depth > best_alpha) {
                best_alpha = depth;
                best_mask = cur_mask;
            }
            return;
        }
        if (depth + popcnt128(P) <= best_alpha) return;

        int order[MAX_N];
        int color[MAX_N];
        int m = 0, c = 0;
        __uint128_t U = P;
        while (U) {
            c++;
            __uint128_t Q = U;
            while (Q) {
                int v = ctz128(Q);
                order[m] = v;
                color[m] = c;
                m++;
                U ^= bit128(v);
                Q &= adj_G[v];
            }
        }

        if (depth + c <= best_alpha) return;

        if (c == 1) {
            if (depth + 1 > best_alpha) {
                best_alpha = depth + 1;
                best_mask = cur_mask | bit128(order[0]);
            }
            return;
        }
        if (c == 2) {
            if (depth + 2 > best_alpha) {
                __uint128_t rem = P;
                while (rem) {
                    int v = ctz128(rem);
                    rem ^= bit128(v);
                    __uint128_t nb = rem & comp_adj[v];
                    if (nb) {
                        int w = ctz128(nb);
                        best_alpha = depth + 2;
                        best_mask = cur_mask | bit128(v) | bit128(w);
                        return;
                    }
                }
                if (depth + 1 > best_alpha) {
                    best_alpha = depth + 1;
                    best_mask = cur_mask | bit128(order[0]);
                }
            }
            return;
        }

        for (int i = m - 1; i >= 0; --i) {
            if (depth + color[i] <= best_alpha) return;
            int v = order[i];
            P ^= bit128(v);
            __uint128_t next_P = P & comp_adj[v];
            if (next_P) {
                expand(next_P, depth + 1, cur_mask | bit128(v));
            } else {
                if (depth + 1 > best_alpha) {
                    best_alpha = depth + 1;
                    best_mask = cur_mask | bit128(v);
                }
            }
            if (target_stop > 0 && best_alpha >= target_stop) return;
        }
    }

    int exact_alpha(vector<int64_t>* out_witness = nullptr) {
        best_alpha = 0;
        best_mask = 0;
        target_stop = 0;
        nodes_visited = 0;
        if (n == 0) return 0;

        __uint128_t cand = full_mask();
        __uint128_t seed = 0;
        int seed_sz = 0;
        while (cand) {
            int best_v = -1, best_d = -1;
            __uint128_t tmp = cand;
            while (tmp) {
                int v = ctz128(tmp);
                tmp ^= bit128(v);
                int d = popcnt128(cand & comp_adj[v]);
                if (d > best_d) {
                    best_d = d;
                    best_v = v;
                }
            }
            seed |= bit128(best_v);
            seed_sz++;
            cand &= comp_adj[best_v];
        }
        best_alpha = seed_sz;
        best_mask = seed;

        expand(full_mask(), 0, 0);

        if (out_witness) {
            out_witness->clear();
            __uint128_t tmp = best_mask;
            while (tmp) {
                int v = ctz128(tmp);
                tmp ^= bit128(v);
                out_witness->push_back(elements[v]);
            }
            sort(out_witness->begin(), out_witness->end());
        }
        return best_alpha;
    }

    bool has_indep_ge(int k, vector<int64_t>* out_witness = nullptr) {
        if (k <= 0) return true;
        if (k > n) return false;
        best_alpha = k - 1;
        best_mask = 0;
        target_stop = k;
        nodes_visited = 0;

        // Fast greedy check first
        __uint128_t cand = full_mask();
        __uint128_t seed = 0;
        int seed_sz = 0;
        while (cand) {
            int best_v = -1, best_d = -1;
            __uint128_t tmp = cand;
            while (tmp) {
                int v = ctz128(tmp);
                tmp ^= bit128(v);
                int d = popcnt128(cand & comp_adj[v]);
                if (d > best_d) { best_d = d; best_v = v; }
            }
            seed |= bit128(best_v);
            seed_sz++;
            cand &= comp_adj[best_v];
        }
        if (seed_sz >= k) {
            best_alpha = seed_sz;
            best_mask = seed;
            if (out_witness) {
                out_witness->clear();
                __uint128_t tmp = best_mask;
                while (tmp) {
                    int v = ctz128(tmp);
                    tmp ^= bit128(v);
                    out_witness->push_back(elements[v]);
                }
                sort(out_witness->begin(), out_witness->end());
            }
            return true;
        }

        expand(full_mask(), 0, 0);
        if (best_alpha >= k) {
            if (out_witness) {
                out_witness->clear();
                __uint128_t tmp = best_mask;
                while (tmp) {
                    int v = ctz128(tmp);
                    tmp ^= bit128(v);
                    out_witness->push_back(elements[v]);
                }
                sort(out_witness->begin(), out_witness->end());
            }
            return true;
        }
        return false;
    }

    void count_k_rec(__uint128_t P, int depth, int target_k, uint64_t& count, uint64_t cap,
                     __uint128_t cur_mask, vector<__uint128_t>* samples, int max_samples) {
        if (count >= cap) return;
        int need = target_k - depth;
        if (need == 0) {
            count++;
            if (samples && (int)samples->size() < max_samples) samples->push_back(cur_mask);
            return;
        }
        if (popcnt128(P) < need) return;
        if (need == 1) {
            int sz = popcnt128(P);
            if (samples && (int)samples->size() < max_samples) {
                __uint128_t tmp = P;
                while (tmp && (int)samples->size() < max_samples) {
                    int v = ctz128(tmp);
                    samples->push_back(cur_mask | bit128(v));
                    tmp ^= bit128(v);
                }
            }
            count += (uint64_t)sz;
            return;
        }
        if (need == 2) {
            __uint128_t rem = P;
            while (rem) {
                int v = ctz128(rem);
                rem ^= bit128(v);
                __uint128_t nb = rem & comp_adj[v];
                int c2 = popcnt128(nb);
                if (c2 > 0) {
                    if (samples && (int)samples->size() < max_samples) {
                        __uint128_t t = nb;
                        while (t && (int)samples->size() < max_samples) {
                            int w = ctz128(t);
                            samples->push_back(cur_mask | bit128(v) | bit128(w));
                            t ^= bit128(w);
                        }
                    }
                    count += (uint64_t)c2;
                    if (count >= cap) return;
                }
            }
            return;
        }

        int order[MAX_N];
        int color[MAX_N];
        int m = 0, c = 0;
        __uint128_t U = P;
        while (U) {
            c++;
            __uint128_t Q = U;
            while (Q) {
                int v = ctz128(Q);
                order[m] = v;
                color[m] = c;
                m++;
                U ^= bit128(v);
                Q &= adj_G[v];
            }
        }
        if (c < need) return;

        for (int i = m - 1; i >= 0; --i) {
            if (color[i] < need) return;
            int v = order[i];
            P ^= bit128(v);
            __uint128_t next_P = P & comp_adj[v];
            if (popcnt128(next_P) >= need - 1) {
                count_k_rec(next_P, depth + 1, target_k, count, cap, cur_mask | bit128(v), samples, max_samples);
                if (count >= cap) return;
            }
        }
    }

    uint64_t count_indep(int target_k, uint64_t cap = UINT64_MAX,
                         vector<__uint128_t>* samples = nullptr, int max_samples = 0) {
        if (target_k <= 0) return (target_k == 0) ? 1 : 0;
        if (target_k > n) return 0;
        if (samples) samples->clear();
        uint64_t count = 0;
        count_k_rec(full_mask(), 0, target_k, count, cap, 0, samples, max_samples);
        return min(count, cap);
    }

    bool naive_has_k_rec(int start, int depth, __uint128_t mask, int target_k) const {
        if (depth == target_k) return true;
        int need = target_k - depth;
        if (popcnt128(mask) < need) return false;
        __uint128_t cand = mask & ((~(__uint128_t)0) << start);
        while (cand) {
            int v = ctz128(cand);
            cand ^= bit128(v);
            if (naive_has_k_rec(v + 1, depth + 1, mask & comp_adj[v], target_k)) return true;
        }
        return false;
    }

    bool naive_has_k(int target_k) const {
        if (target_k > n) return false;
        __uint128_t all = full_mask();
        for (int v = 0; v <= n - target_k; ++v) {
            if (naive_has_k_rec(v + 1, 1, all & comp_adj[v], target_k)) return true;
        }
        return false;
    }
};

bool verify_witness_indep(const vector<int64_t>& A, const vector<int64_t>& B) {
    set<int64_t> sA(A.begin(), A.end());
    for (int64_t b : B) if (!sA.count(b)) return false;
    for (size_t i = 0; i < B.size(); ++i) {
        for (size_t j = i + 1; j < B.size(); ++j) {
            if (sA.count(B[i] + B[j])) return false;
        }
    }
    return true;
}

static inline void normalize_set(vector<int64_t>& A) {
    sort(A.begin(), A.end());
    A.erase(unique(A.begin(), A.end()), A.end());
}

static inline vector<int64_t> build_sym(const vector<int64_t>& P, bool include_zero) {
    vector<int64_t> A;
    A.reserve(2 * P.size() + (include_zero ? 1 : 0));
    for (int i = (int)P.size() - 1; i >= 0; --i) A.push_back(-P[i]);
    if (include_zero) A.push_back(0);
    for (size_t i = 0; i < P.size(); ++i) A.push_back(P[i]);
    return A;
}

static const map<int, vector<int64_t>> KNOWN_WITNESSES = {
    {3, {-1, 0, 1}},
    {7, {-3, -2, -1, 0, 1, 2, 3}},
    {13, {-9, -6, -5, -4, -3, -1, 0, 1, 2, 3, 5, 7, 8}},
    {21, {-15, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15}},
    {31, {-30, -18, -16, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 30}},
    {43, {-42, -26, -24, -22, -20, -18, -16, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 20, 22, 24, 26, 42}},
    {51, {-66, -48, -42, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 42, 48, 66}}
};

// ============================================================
// Algebraic & Geometric Construction Generators
// ============================================================

void gen_lp_sphere_rec(int d, int L, int p, int64_t rem, int idx, vector<int>& cur, vector<vector<int>>& pts) {
    if (idx == d) {
        if (rem == 0) pts.push_back(cur);
        return;
    }
    int64_t max_single = 1;
    for (int t = 0; t < p; ++t) max_single *= L;
    if (rem < 0 || rem > (int64_t)(d - idx) * max_single) return;
    for (int x = -L; x <= L; ++x) {
        int64_t xp = 1;
        int ax = abs(x);
        for (int t = 0; t < p; ++t) xp *= ax;
        if (xp <= rem) {
            cur[idx] = x;
            gen_lp_sphere_rec(d, L, p, rem - xp, idx + 1, cur, pts);
        }
    }
}

vector<vector<int>> get_lp_sphere(int d, int L, int p, int64_t R_p) {
    vector<vector<int>> pts;
    vector<int> cur(d, 0);
    gen_lp_sphere_rec(d, L, p, R_p, 0, cur, pts);
    return pts;
}

vector<int64_t> project_points(const vector<vector<int>>& pts, const vector<int64_t>& weights) {
    vector<int64_t> res;
    res.reserve(pts.size());
    for (const auto& pt : pts) {
        int64_t val = 0;
        for (size_t i = 0; i < pt.size(); ++i) val += (int64_t)pt[i] * weights[i];
        res.push_back(val);
    }
    normalize_set(res);
    return res;
}

vector<int64_t> prune_to_size(vector<int64_t> A, int target_n, TinySet& sA) {
    normalize_set(A);
    while ((int)A.size() > target_n) {
        int sz = (int)A.size();
        sA.clear();
        for (int64_t x : A) sA.insert(x);
        vector<int> score(sz, 0);
        for (int i = 0; i < sz; ++i) {
            for (int j = i + 1; j < sz; ++j) {
                int64_t sm = A[i] + A[j];
                if (sA.contains(sm)) {
                    score[i]++;
                    score[j]++;
                    auto it = lower_bound(A.begin(), A.end(), sm);
                    if (it != A.end() && *it == sm) score[it - A.begin()]++;
                }
            }
        }
        int min_idx = 0;
        for (int i = 1; i < sz; ++i) {
            if (score[i] < score[min_idx]) min_idx = i;
        }
        A.erase(A.begin() + min_idx);
    }
    return A;
}

// Ternary Golay G_11 generator matrix (6x11 over F_3) -> 729 codewords -> mapped to {-1,0,1}^11
vector<vector<int>> get_ternary_golay_11_weight(int target_weight) {
    // Parity-check / generator for ternary Golay G_11 (systematic [I_5 | P] or [I_6 | ...] wait: G_11 is [11, 6, 5])
    static const int G[6][11] = {
        {1,0,0,0,0,0, 1,1,1,1,1},
        {0,1,0,0,0,0, 0,1,2,2,1},
        {0,0,1,0,0,0, 1,0,1,2,2},
        {0,0,0,1,0,0, 2,1,0,1,2},
        {0,0,0,0,1,0, 2,2,1,0,1},
        {0,0,0,0,0,1, 1,2,2,1,0}
    };
    vector<vector<int>> pts;
    int coeff[6];
    for (int mask = 0; mask < 729; ++mask) {
        int tmp = mask;
        for (int i = 0; i < 6; ++i) { coeff[i] = tmp % 3; tmp /= 3; }
        vector<int> w(11, 0);
        int wt = 0;
        for (int j = 0; j < 11; ++j) {
            int s = 0;
            for (int i = 0; i < 6; ++i) s += coeff[i] * G[i][j];
            s %= 3;
            if (s == 2) s = -1;
            w[j] = s;
            if (s != 0) wt++;
        }
        if (wt == target_weight) pts.push_back(w);
    }
    return pts;
}

// Extended Binary Golay G_24 generator matrix (12x24) -> wait: 4096 codewords; weight 8 has 759 words
vector<vector<int>> get_binary_golay_24_weight8() {
    // Standard 12x12 circulant matrix B for extended binary Golay [24, 12, 8]
    static const int B_row0[11] = {1,1,0,1,1,1,0,0,0,1,0};
    int G[12][24];
    memset(G, 0, sizeof(G));
    for (int i = 0; i < 12; ++i) {
        G[i][i] = 1;
        if (i < 11) {
            for (int j = 0; j < 11; ++j) G[i][12 + j] = B_row0[(j - i + 11) % 11];
            G[i][23] = 1;
        } else {
            for (int j = 0; j < 11; ++j) G[i][12 + j] = 1;
            G[i][23] = 0;
        }
    }
    vector<vector<int>> pts;
    for (int mask = 0; mask < 4096; ++mask) {
        vector<int> w(24, 0);
        int wt = 0;
        for (int j = 0; j < 24; ++j) {
            int s = 0;
            for (int i = 0; i < 12; ++i) {
                if ((mask >> i) & 1) s ^= G[i][j];
            }
            w[j] = s;
            wt += s;
        }
        if (wt == 8) pts.push_back(w);
    }
    return pts;
}

struct CandEntry {
    vector<int64_t> A;
    string name;
};

static inline int turan_min_edges(int n, int max_alpha) {
    if (max_alpha <= 0) return n * (n - 1) / 2;
    if (max_alpha >= n) return 0;
    int q = n / max_alpha;
    int r = n % max_alpha;
    return r * (q + 1) * q / 2 + (max_alpha - r) * q * (q - 1) / 2;
}

void run_algebraic_sweep(int n_min, int n_max, const string& out_path) {
    auto t0 = chrono::steady_clock::now();
    int n_gen_max = min(MAX_N, n_max + 8);
    cout << "=== Running Parallel Algebraic & Geometric Construction Sweep for n in [" << n_min << ", " << n_max << "] (gen up to " << n_gen_max << ") ===" << endl;

    vector<CandEntry> cands;
    auto push_cand = [&](vector<int64_t> A, const string& name) {
        normalize_set(A);
        int n = (int)A.size();
        if (n >= n_min && n <= n_gen_max && n <= MAX_N) {
            cands.push_back({move(A), name});
        }
    };

    // 1. Glued pairs & triples of known optimal witnesses A_3..A_51 (including dyadic M=2,3,4 overlaps!)
    vector<int> known_sizes = {3, 7, 13, 21, 31, 43, 51};
    for (int n1 : known_sizes) {
        const auto& A1 = KNOWN_WITNESSES.at(n1);
        for (int n2 : known_sizes) {
            const auto& A2 = KNOWN_WITNESSES.at(n2);
            for (int64_t M : {1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 17, 23, 37, 50, 100, 1000}) {
                vector<int64_t> glued = A1;
                for (int64_t x : A2) glued.push_back(M * x);
                push_cand(glued, "glued_" + to_string(n1) + "+" + to_string(n2) + "_M" + to_string(M));
                vector<int64_t> glued_sh = A1;
                for (int64_t x : A2) if (x != 0) glued_sh.push_back(M * x + 1);
                push_cand(glued_sh, "glued_sh_" + to_string(n1) + "+" + to_string(n2) + "_M" + to_string(M));
            }
        }
    }

    // Triple glued (including overlapping dyadic/triadic M1, M2 in {2,3,4,5,10,100})
    for (int n1 : {13, 21, 31, 43, 51}) {
        for (int n2 : {13, 21, 31, 43, 51}) {
            for (int n3 : {7, 13, 21, 31, 43, 51}) {
                for (auto [M1, M2] : vector<pair<int64_t,int64_t>>{{2,4},{2,6},{2,8},{3,6},{3,9},{4,8},{2,100},{10,100},{100,10000}}) {
                    vector<int64_t> glued = KNOWN_WITNESSES.at(n1);
                    for (int64_t x : KNOWN_WITNESSES.at(n2)) if (x != 0) glued.push_back(M1 * x);
                    for (int64_t x : KNOWN_WITNESSES.at(n3)) if (x != 0) glued.push_back(M2 * x);
                    push_cand(glued, "glued3_" + to_string(n1) + "+" + to_string(n2) + "+" + to_string(n3) + "_M" + to_string(M1) + "_" + to_string(M2));
                }
            }
        }
    }

    // 2. Generalized A_k structure: [-C..C] U +- {C+2, ..., E} U +- {outliers}
    for (int C = 10; C <= 38; C += 1) {
        for (int tail = 0; tail <= 20; ++tail) {
            vector<int64_t> P;
            for (int x = 1; x <= C; ++x) P.push_back(x);
            for (int t = 1; t <= tail; ++t) P.push_back(C + 2 * t);
            int max_e = P.back();
            push_cand(build_sym(P, true), "sym_core_C" + to_string(C) + "_T" + to_string(tail));
            if (2 * (int)P.size() + 3 <= n_max) {
                for (int out1 = max_e + 2; out1 <= 2 * max_e; out1 += 4) {
                    auto P1 = P;
                    P1.push_back(out1);
                    push_cand(build_sym(P1, true), "sym_core1_C" + to_string(C));
                    if (2 * (int)P1.size() + 3 <= n_max) {
                        for (int out2 = out1 + 4; out2 <= 2 * out1; out2 += 6) {
                            auto P2 = P1;
                            P2.push_back(out2);
                            push_cand(build_sym(P2, true), "sym_core2_C" + to_string(C));
                            if (2 * (int)P2.size() + 3 <= n_max && C >= 18 && tail >= 6 && (out1 % 4 == 0)) {
                                for (int out3 = out2 + 6; out3 <= min(2 * out2, 220); out3 += 12) {
                                    auto P3 = P2;
                                    P3.push_back(out3);
                                    push_cand(build_sym(P3, true), "sym_core3_C" + to_string(C));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // 3. Discrete Spheres (L2, L1, L4) & Concentric Multi-Shell Spheres projected via B = 2..3L+1
    struct SphereCfg { int d, L, p; vector<int64_t> Rlist; };
    vector<SphereCfg> s_cfgs = {
        {2, 12, 2, {25, 50, 65, 85, 100, 125, 130, 145, 169}},
        {3, 3, 2, {6, 10, 11, 14, 17, 18, 19, 21, 22}},
        {3, 4, 2, {10, 14, 18, 22, 26, 29, 30, 34, 38}},
        {4, 2, 2, {4, 5, 6, 7, 8, 9, 10}},
        {4, 3, 2, {6, 10, 12, 14, 18}},
        {5, 1, 2, {2, 3, 4}},
        {5, 2, 2, {4, 5, 6, 8}},
        {6, 1, 2, {2, 3, 4}},
        {6, 2, 2, {4, 6}},
        {7, 1, 2, {2, 3}},
        {8, 1, 2, {2, 3}},
        {3, 4, 1, {4, 5, 6}},
        {4, 3, 1, {3, 4, 5}},
        {5, 2, 1, {3, 4}},
        {4, 2, 4, {17, 18, 20}}
    };

    mt19937_64 rng(202501);
    TinySet tmp_sA;
    for (const auto& sc : s_cfgs) {
        for (size_t idx = 0; idx < sc.Rlist.size(); ++idx) {
            auto pts = get_lp_sphere(sc.d, sc.L, sc.p, sc.Rlist[idx]);
            if (pts.empty()) continue;
            vector<vector<vector<int>>> pt_sets = {pts};
            auto pts0 = pts;
            pts0.push_back(vector<int>(sc.d, 0));
            pt_sets.push_back(pts0);
            if (idx + 1 < sc.Rlist.size()) {
                auto pts2 = get_lp_sphere(sc.d, sc.L, sc.p, sc.Rlist[idx + 1]);
                if (!pts2.empty() && pts.size() + pts2.size() <= 160) {
                    auto u = pts;
                    u.insert(u.end(), pts2.begin(), pts2.end());
                    pt_sets.push_back(u);
                    u.push_back(vector<int>(sc.d, 0));
                    pt_sets.push_back(u);
                }
            }

            for (size_t si = 0; si < pt_sets.size(); ++si) {
                const auto& cur_pts = pt_sets[si];
                int maxB = 3 * sc.L + 1;
                for (int B = 2; B <= maxB; ++B) {
                    vector<int64_t> w(sc.d, 1);
                    for (int k = 1; k < sc.d; ++k) w[k] = w[k - 1] * B;
                    auto A = project_points(cur_pts, w);
                    if ((int)A.size() >= n_min && (int)A.size() <= n_max) {
                        push_cand(A, "sphere_d" + to_string(sc.d) + "_p" + to_string(sc.p) + "_B" + to_string(B));
                    } else if ((int)A.size() > n_max && (int)A.size() <= 160) {
                        for (int tgt : {100, 90, 80, 70, 60, 57, 52}) {
                            if (tgt >= n_min && tgt <= n_max && tgt < (int)A.size()) {
                                push_cand(prune_to_size(A, tgt, tmp_sA), "sphere_pruned_d" + to_string(sc.d) + "_B" + to_string(B));
                            }
                        }
                    }
                }
                if (cur_pts.size() >= (size_t)n_min) {
                    for (int trial = 0; trial < 30; ++trial) {
                        vector<int64_t> w(sc.d);
                        for (int k = 0; k < sc.d; ++k) w[k] = 1 + (int64_t)(rng() % 23);
                        auto A = project_points(cur_pts, w);
                        if ((int)A.size() >= n_min && (int)A.size() <= n_max) {
                            push_cand(A, "sphere_linproj_d" + to_string(sc.d));
                        }
                    }
                }
            }
        }
    }

    // 4. Modular / Paley Quadratic Residue & Dense Residue Mask Constructions
    vector<int> primes = {53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199};
    for (int p : primes) {
        set<int> qr;
        for (int x = 1; x < p; ++x) qr.insert((x * x) % p);
        for (int len = p / 2; len <= p; len += 5) {
            vector<int64_t> A_qr, A_nqr;
            for (int x = -len; x <= len; ++x) {
                int r = ((x % p) + p) % p;
                if (r == 0 || qr.count(r)) A_qr.push_back(x);
                if (r == 0 || !qr.count(r)) A_nqr.push_back(x);
            }
            push_cand(A_qr, "paley_qr_p" + to_string(p));
            push_cand(A_nqr, "paley_nqr_p" + to_string(p));
        }
    }

    // 5. Ternary Golay G_11 (weight 5 -> 132 pts, weight 6 -> 132 pts) & Binary Golay G_24 & RM(1,m)
    for (int wt : {5, 6}) {
        auto g11 = get_ternary_golay_11_weight(wt);
        g11.push_back(vector<int>(11, 0));
        for (int B : {2, 3, 4}) {
            vector<int64_t> w(11, 1);
            for (int k = 1; k < 11; ++k) w[k] = w[k - 1] * B;
            auto A = project_points(g11, w);
            if ((int)A.size() >= n_min && (int)A.size() <= n_max)
                push_cand(A, "golay11_w" + to_string(wt) + "_B" + to_string(B));
        }
        for (int trial = 0; trial < 40; ++trial) {
            vector<int64_t> w(11);
            for (int k = 0; k < 11; ++k) w[k] = 1 + (int64_t)(rng() % 20);
            auto A = project_points(g11, w);
            if ((int)A.size() >= n_min && (int)A.size() <= n_max)
                push_cand(A, "golay11_w" + to_string(wt) + "_lin");
        }
    }
    {
        auto g24 = get_binary_golay_24_weight8();
        g24.push_back(vector<int>(24, 0));
        for (int trial = 0; trial < 60; ++trial) {
            vector<int64_t> w(24);
            for (int k = 0; k < 24; ++k) w[k] = -10 + (int64_t)(rng() % 21);
            auto A = project_points(g24, w);
            if ((int)A.size() >= n_min && (int)A.size() <= n_max)
                push_cand(A, "golay24_lin");
        }
    }
    for (int m : {4, 5, 6}) {
        int dim = 1 << m;
        vector<vector<int>> pts;
        for (int mask = 0; mask < (1 << (m + 1)); ++mask) {
            bool flip = (mask >> m) & 1;
            vector<int> v(dim);
            for (int j = 0; j < dim; ++j) {
                int dot = __builtin_popcount(j & (mask & ((1 << m) - 1))) & 1;
                v[j] = (dot ^ (flip ? 1 : 0)) ? 1 : -1;
            }
            pts.push_back(v);
        }
        pts.push_back(vector<int>(dim, 0));
        for (int trial = 0; trial < 40; ++trial) {
            vector<int64_t> w(dim);
            for (int j = 0; j < dim; ++j) w[j] = 1 + (int64_t)(rng() % 40);
            auto A = project_points(pts, w);
            if ((int)A.size() >= n_min && (int)A.size() <= n_max)
                push_cand(A, "rm1_m" + to_string(m));
        }
    }

    // 6. Singer Difference Sets for q=7 (v=57), q=8 (v=73), q=9 (v=91) + dense complements
    // Known Singer difference set for PG(2,7) mod 57: {0,1,3,13,32,36,43,52}, complement mod 57 has size 49
    // More generally, modular intervals/Sidon-complements mod m in [52..100]
    for (int modv = 53; modv <= 100; ++modv) {
        // Quadratic residues + shifts centered
        vector<int64_t> A_c;
        for (int x = -(modv / 2); x <= (modv - 1) / 2; ++x) A_c.push_back(x);
        push_cand(A_c, "interval_" + to_string(modv));
    }

    cout << "Generated " << cands.size() << " candidate sets. Evaluating in parallel..." << endl;

    vector<int> global_best_alpha(MAX_N + 1, 999999);
    vector<vector<int64_t>> global_best_A(MAX_N + 1);
    vector<string> global_best_method(MAX_N + 1);

    #pragma omp parallel
    {
        TinySet sA;
        Graph128 g;
        #pragma omp for schedule(dynamic, 32)
        for (int idx = 0; idx < (int)cands.size(); ++idx) {
            int n = (int)cands[idx].A.size();
            int cur_best;
            #pragma omp atomic read
            cur_best = global_best_alpha[n];

            g.build(cands[idx].A, sA, 2);
            if (cur_best < 999999) {
                if (g.edges_G < turan_min_edges(n, cur_best - 1)) continue;
                if (g.has_indep_ge(cur_best)) continue;
            }
            int a = g.exact_alpha();
            #pragma omp critical
            {
                if (a < global_best_alpha[n]) {
                    global_best_alpha[n] = a;
                    global_best_A[n] = cands[idx].A;
                    global_best_method[n] = cands[idx].name;
                }
            }
        }
    }

    // Downward 1-element deletion pass (propagates odd winners like n=55, 65, 79, 89, 95, 101 -> even n!)
    for (int pass = 0; pass < 3; ++pass) {
        for (int n = n_gen_max; n >= n_min + 1; --n) {
            if (global_best_alpha[n] >= 999999) continue;
            const auto& cur = global_best_A[n];
            int cur_b = global_best_alpha[n - 1];
            vector<int64_t> best_sub_A;
            #pragma omp parallel
            {
                TinySet lsA;
                Graph128 lg;
                #pragma omp for schedule(dynamic, 2)
                for (int rem = 0; rem < n; ++rem) {
                    vector<int64_t> cand;
                    cand.reserve(n - 1);
                    for (int j = 0; j < n; ++j) if (j != rem) cand.push_back(cur[j]);
                    lg.build(cand, lsA, 2);
                    int b;
                    #pragma omp atomic read
                    b = cur_b;
                    if (b < 999999) {
                        if (lg.edges_G < turan_min_edges(n - 1, b - 1)) continue;
                        if (lg.has_indep_ge(b)) continue;
                    }
                    int a = lg.exact_alpha();
                    #pragma omp critical
                    {
                        if (a < cur_b) {
                            cur_b = a;
                            best_sub_A = cand;
                        }
                    }
                }
            }
            if (!best_sub_A.empty()) {
                global_best_alpha[n - 1] = cur_b;
                global_best_A[n - 1] = best_sub_A;
                global_best_method[n - 1] = "del_from_" + to_string(n);
            }
        }
    }

    // Upward 1-element addition pass (tries adding elements in [-150, 150] or hot sums to best[n-1])
    for (int pass = 0; pass < 2; ++pass) {
        for (int n = n_min; n <= n_max - 1; ++n) {
            if (global_best_alpha[n] >= 999999) continue;
            const auto& cur = global_best_A[n];
            int cur_b = global_best_alpha[n + 1];
            if (cur_b <= global_best_alpha[n]) continue;
            int64_t lim = 120;
            for (int64_t x : cur) lim = max(lim, min<int64_t>(200, llabs(x) + 20));
            vector<int64_t> best_sup_A;
            #pragma omp parallel
            {
                TinySet lsA;
                Graph128 lg;
                #pragma omp for schedule(dynamic, 8)
                for (int64_t add_v = -lim; add_v <= lim; ++add_v) {
                    if (binary_search(cur.begin(), cur.end(), add_v)) continue;
                    vector<int64_t> cand = cur;
                    cand.push_back(add_v);
                    sort(cand.begin(), cand.end());
                    lg.build(cand, lsA, 2);
                    int b;
                    #pragma omp atomic read
                    b = cur_b;
                    if (b < 999999) {
                        if (lg.edges_G < turan_min_edges(n + 1, b - 1)) continue;
                        if (lg.has_indep_ge(b)) continue;
                    }
                    int a = lg.exact_alpha();
                    #pragma omp critical
                    {
                        if (a < cur_b) {
                            cur_b = a;
                            best_sup_A = cand;
                        }
                    }
                }
            }
            if (!best_sup_A.empty()) {
                global_best_alpha[n + 1] = cur_b;
                global_best_A[n + 1] = best_sup_A;
                global_best_method[n + 1] = "add_from_" + to_string(n);
            }
        }
    }

    double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    cout << "\nAlgebraic Sweep Best Results (" << fixed << setprecision(2) << elapsed << " s):" << endl;
    ofstream fout(out_path);
    for (int n = n_min; n <= n_max; ++n) {
        if (global_best_alpha[n] < 999999) {
            cout << "  n=" << setw(3) << n << " | alpha=" << setw(2) << global_best_alpha[n]
                 << " | method=" << global_best_method[n] << endl;
            fout << n << " " << global_best_alpha[n] << " " << global_best_method[n];
            for (int64_t x : global_best_A[n]) fout << " " << x;
            fout << "\n";
        }
    }
}

struct SearchConfig {
    int n = 52;
    int target_alpha = 7;
    int mode = 0; // 0 = asymmetric, 1 = symmetric (odd with 0, or even without 0), 2 = asym with 0 fixed
    int64_t U = 100;
    int seconds = 10;
    uint64_t count_cap = 4096;
    int max_samples = 64;
    uint64_t seed_rng = 42;
    bool quiet = false;
};

struct SearchResult {
    bool found_target = false;
    int best_alpha = 999999;
    uint64_t best_count = UINT64_MAX;
    vector<int64_t> best_A;
};

SearchResult run_sa_search(const SearchConfig& cfg, const vector<vector<int64_t>>& initial_seeds) {
    SearchResult res;
    int n = cfg.n;
    bool is_sym = (cfg.mode == 1);
    bool sym_zero = (n % 2 == 1);
    int m = is_sym ? (n / 2) : n;

    auto t_start = chrono::steady_clock::now();
    volatile bool global_found = false;
    int global_best_alpha = 999999;
    uint64_t global_best_count = UINT64_MAX;
    vector<int64_t> global_best_A;

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        mt19937_64 rng(cfg.seed_rng + (uint64_t)tid * 104729ULL + 7919ULL);
        uniform_real_distribution<double> u01(0.0, 1.0);

        TinySet sA;
        Graph128 g;
        vector<int64_t> cur_state;

        auto init_state = [&](int restart_idx) {
            cur_state.clear();
            if (!initial_seeds.empty() && (restart_idx == 0 || (restart_idx % 3 != 2))) {
                const auto& seed_A = initial_seeds[(tid + restart_idx) % initial_seeds.size()];
                if (is_sym) {
                    set<int64_t> pos;
                    for (int64_t x : seed_A) {
                        if (x > 0 && x <= cfg.U) pos.insert(x);
                        else if (x < 0 && -x <= cfg.U) pos.insert(-x);
                    }
                    cur_state.assign(pos.begin(), pos.end());
                    while ((int)cur_state.size() > m) {
                        cur_state.erase(cur_state.begin() + (rng() % cur_state.size()));
                    }
                    while ((int)cur_state.size() < m) {
                        int64_t v = 1 + (int64_t)(rng() % cfg.U);
                        if (find(cur_state.begin(), cur_state.end(), v) == cur_state.end())
                            cur_state.push_back(v);
                    }
                    sort(cur_state.begin(), cur_state.end());
                    if (tid > 0 || restart_idx > 0) {
                        int k_pert = 1 + (int)(rng() % min(4, m));
                        for (int p = 0; p < k_pert; ++p) {
                            int idx = (int)(rng() % m);
                            int64_t v = 1 + (int64_t)(rng() % cfg.U);
                            if (find(cur_state.begin(), cur_state.end(), v) == cur_state.end())
                                cur_state[idx] = v;
                        }
                        sort(cur_state.begin(), cur_state.end());
                    }
                } else {
                    set<int64_t> elems;
                    for (int64_t x : seed_A) {
                        if (x >= -cfg.U && x <= cfg.U) elems.insert(x);
                    }
                    if (cfg.mode == 2) elems.insert(0);
                    cur_state.assign(elems.begin(), elems.end());
                    while ((int)cur_state.size() > n) {
                        int idx = (int)(rng() % cur_state.size());
                        if (cfg.mode == 2 && cur_state[idx] == 0) continue;
                        cur_state.erase(cur_state.begin() + idx);
                    }
                    while ((int)cur_state.size() < n) {
                        int64_t v = -(cfg.U) + (int64_t)(rng() % (2 * cfg.U + 1));
                        if (find(cur_state.begin(), cur_state.end(), v) == cur_state.end())
                            cur_state.push_back(v);
                    }
                    sort(cur_state.begin(), cur_state.end());
                    if (tid > 0 || restart_idx > 0) {
                        int k_pert = 1 + (int)(rng() % min(5, n));
                        for (int p = 0; p < k_pert; ++p) {
                            int idx = (int)(rng() % n);
                            if (cfg.mode == 2 && cur_state[idx] == 0) continue;
                            int64_t v = -(cfg.U) + (int64_t)(rng() % (2 * cfg.U + 1));
                            if (find(cur_state.begin(), cur_state.end(), v) == cur_state.end())
                                cur_state[idx] = v;
                        }
                        sort(cur_state.begin(), cur_state.end());
                    }
                }
            } else {
                set<int64_t> s;
                if (is_sym) {
                    int core = min((int)cfg.U, max(4, m / 2));
                    for (int i = 1; i <= core; ++i) s.insert(i);
                    while ((int)s.size() < m) s.insert(1 + (int64_t)(rng() % cfg.U));
                } else {
                    if (cfg.mode == 2) s.insert(0);
                    int core = min((int)cfg.U, max(4, n / 4));
                    for (int i = -core; i <= core && (int)s.size() < n; ++i) s.insert(i);
                    while ((int)s.size() < n) s.insert(-(cfg.U) + (int64_t)(rng() % (2 * cfg.U + 1)));
                }
                cur_state.assign(s.begin(), s.end());
            }
        };

        auto eval_state = [&](const vector<int64_t>& st, int max_allowed_alpha,
                              int& out_alpha, uint64_t& out_cnt,
                              vector<__uint128_t>& out_samples, vector<int64_t>& out_A,
                              vector<int64_t>& out_hot_sums) -> bool {
            if (is_sym) out_A = build_sym(st, sym_zero);
            else out_A = st;

            g.build(out_A, sA, 2);
            if (max_allowed_alpha < 999999 && g.has_indep_ge(max_allowed_alpha + 1)) {
                return false;
            }
            out_alpha = g.exact_alpha();
            if (out_alpha <= cfg.target_alpha) {
                out_cnt = 0;
                return true;
            }
            out_cnt = g.count_indep(out_alpha, cfg.count_cap, &out_samples, cfg.max_samples);

            out_hot_sums.clear();
            if (!out_samples.empty()) {
                map<int64_t, int> sum_freq;
                for (__uint128_t mask : out_samples) {
                    int verts[MAX_N];
                    int nv = 0;
                    __uint128_t tmp = mask;
                    while (tmp) {
                        int v = ctz128(tmp);
                        tmp ^= bit128(v);
                        verts[nv++] = v;
                    }
                    for (int i = 0; i < nv; ++i) {
                        for (int j = i + 1; j < nv; ++j) {
                            int64_t sm = g.elements[verts[i]] + g.elements[verts[j]];
                            int64_t key = is_sym ? llabs(sm) : sm;
                            if (is_sym) {
                                if (key >= 1 && key <= cfg.U && !sA.contains(key))
                                    sum_freq[key]++;
                            } else {
                                if (key >= -cfg.U && key <= cfg.U && !sA.contains(key))
                                    sum_freq[key]++;
                            }
                        }
                    }
                }
                vector<pair<int, int64_t>> ranked;
                ranked.reserve(sum_freq.size());
                for (auto& kv : sum_freq) ranked.push_back({kv.second, kv.first});
                sort(ranked.rbegin(), ranked.rend());
                for (size_t i = 0; i < ranked.size() && i < 16; ++i) {
                    out_hot_sums.push_back(ranked[i].second);
                }
            }
            return true;
        };

        int restart = 0;
        while (!global_found) {
            auto now = chrono::steady_clock::now();
            if (chrono::duration<double>(now - t_start).count() >= cfg.seconds) break;

            init_state(restart++);
            int cur_alpha = 999999;
            uint64_t cur_cnt = UINT64_MAX;
            vector<__uint128_t> cur_samples;
            vector<int64_t> cur_A, cur_hot_sums;
            eval_state(cur_state, 999999, cur_alpha, cur_cnt, cur_samples, cur_A, cur_hot_sums);

            if (cur_alpha <= cfg.target_alpha || cur_alpha < global_best_alpha ||
                (cur_alpha == global_best_alpha && cur_cnt < global_best_count)) {
                #pragma omp critical
                {
                    if (cur_alpha < global_best_alpha ||
                        (cur_alpha == global_best_alpha && cur_cnt < global_best_count)) {
                        global_best_alpha = cur_alpha;
                        global_best_count = cur_cnt;
                        global_best_A = cur_A;
                        if (!cfg.quiet) {
                            cout << "[T" << tid << "] Init best: alpha=" << cur_alpha
                                 << ", cnt=" << cur_cnt << endl;
                        }
                    }
                    if (cur_alpha <= cfg.target_alpha) {
                        global_found = true;
                    }
                }
                if (global_found) break;
            }

            long long no_improve = 0;
            long long max_no_improve = (n <= 60) ? 20000 : 8000;
            long long iter = 0;

            while (!global_found && no_improve < max_no_improve) {
                iter++;
                no_improve++;
                if ((iter & 255) == 0) {
                    auto now2 = chrono::steady_clock::now();
                    if (chrono::duration<double>(now2 - t_start).count() >= cfg.seconds) break;
                }

                vector<int64_t> next_state = cur_state;
                double r_move = u01(rng);
                bool moved = false;

                if (r_move < 0.55 && !cur_hot_sums.empty()) {
                    int top_k = min((int)cur_hot_sums.size(), 6);
                    int64_t add_val = cur_hot_sums[rng() % top_k];
                    if (find(next_state.begin(), next_state.end(), add_val) == next_state.end()) {
                        int rem_idx = (int)(rng() % next_state.size());
                        if (!cur_samples.empty() && u01(rng) < 0.5) {
                            __uint128_t sm = cur_samples[rng() % cur_samples.size()];
                            vector<int64_t> s_vals;
                            while (sm) {
                                int v = ctz128(sm);
                                sm ^= bit128(v);
                                int64_t val = g.elements[v];
                                if (is_sym) {
                                    if (val != 0) s_vals.push_back(llabs(val));
                                } else {
                                    if (!(cfg.mode == 2 && val == 0)) s_vals.push_back(val);
                                }
                            }
                            if (!s_vals.empty()) {
                                int64_t pick_v = s_vals[rng() % s_vals.size()];
                                for (int k = 0; k < (int)next_state.size(); ++k) {
                                    if (next_state[k] == pick_v) { rem_idx = k; break; }
                                }
                            }
                        }
                        if (!(!is_sym && cfg.mode == 2 && next_state[rem_idx] == 0)) {
                            next_state[rem_idx] = add_val;
                            moved = true;
                        }
                    }
                }

                if (!moved && r_move < 0.80) {
                    int rem_idx = (int)(rng() % next_state.size());
                    if (!(!is_sym && cfg.mode == 2 && next_state[rem_idx] == 0)) {
                        int64_t delta = (int64_t)(1 + (rng() % 6)) * ((rng() & 1) ? 1 : -1);
                        int64_t cand = next_state[rem_idx] + delta;
                        bool ok = is_sym ? (cand >= 1 && cand <= cfg.U) : (cand >= -cfg.U && cand <= cfg.U);
                        if (ok && find(next_state.begin(), next_state.end(), cand) == next_state.end()) {
                            next_state[rem_idx] = cand;
                            moved = true;
                        }
                    }
                }

                if (!moved) {
                    int num_swaps = (u01(rng) < 0.15 && next_state.size() >= 4) ? 2 : 1;
                    for (int sw = 0; sw < num_swaps; ++sw) {
                        int rem_idx = (int)(rng() % next_state.size());
                        if (!is_sym && cfg.mode == 2 && next_state[rem_idx] == 0) continue;
                        int64_t cand = is_sym ? (1 + (int64_t)(rng() % cfg.U))
                                              : (-cfg.U + (int64_t)(rng() % (2 * cfg.U + 1)));
                        if (find(next_state.begin(), next_state.end(), cand) == next_state.end()) {
                            next_state[rem_idx] = cand;
                            moved = true;
                        }
                    }
                }

                if (!moved) continue;
                sort(next_state.begin(), next_state.end());

                bool allow_up = (u01(rng) < 0.002);
                int max_allowed = allow_up ? (cur_alpha + 1) : cur_alpha;

                int next_alpha = 999999;
                uint64_t next_cnt = UINT64_MAX;
                vector<__uint128_t> next_samples;
                vector<int64_t> next_A, next_hot_sums;
                if (!eval_state(next_state, max_allowed, next_alpha, next_cnt, next_samples, next_A, next_hot_sums)) {
                    continue;
                }

                bool accept = false;
                if (next_alpha < cur_alpha) {
                    accept = true;
                } else if (next_alpha == cur_alpha) {
                    if (next_cnt <= cur_cnt) {
                        accept = true;
                    } else {
                        double temp = max(1.0, 0.12 * (double)cur_cnt);
                        double prob = exp(-(double)(next_cnt - cur_cnt) / temp);
                        if (u01(rng) < min(0.06, prob)) accept = true;
                    }
                } else if (next_alpha == cur_alpha + 1 && allow_up) {
                    accept = true;
                }

                if (accept) {
                    bool improved_local = (next_alpha < cur_alpha) ||
                                          (next_alpha == cur_alpha && next_cnt < cur_cnt);
                    cur_state = move(next_state);
                    cur_alpha = next_alpha;
                    cur_cnt = next_cnt;
                    cur_samples = move(next_samples);
                    cur_A = move(next_A);
                    cur_hot_sums = move(next_hot_sums);

                    if (improved_local) no_improve = 0;

                    if (cur_alpha <= cfg.target_alpha || cur_alpha < global_best_alpha ||
                        (cur_alpha == global_best_alpha && cur_cnt < global_best_count)) {
                        #pragma omp critical
                        {
                            if (cur_alpha < global_best_alpha ||
                                (cur_alpha == global_best_alpha && cur_cnt < global_best_count)) {
                                global_best_alpha = cur_alpha;
                                global_best_count = cur_cnt;
                                global_best_A = cur_A;
                                if (!cfg.quiet) {
                                    cout << "[T" << tid << " iter=" << iter << "] Best: alpha=" << cur_alpha
                                         << ", cnt=" << cur_cnt << endl;
                                }
                            }
                            if (cur_alpha <= cfg.target_alpha) {
                                global_found = true;
                            }
                        }
                    }
                }
            }
        }
    }

    res.found_target = global_found;
    res.best_alpha = global_best_alpha;
    res.best_count = global_best_count;
    res.best_A = global_best_A;
    return res;
}

void run_selftest() {
    cout << "=== Running Exact 128-bit BBMC Self-Test ===" << endl;
    TinySet sA;
    for (auto& [n, A] : KNOWN_WITNESSES) {
        Graph128 g;
        g.build(A, sA, 2);
        vector<int64_t> wit;
        int alpha = g.exact_alpha(&wit);
        bool wit_ok = verify_witness_indep(A, wit) && ((int)wit.size() == alpha);
        uint64_t c_alpha = g.count_indep(alpha);
        uint64_t c_next = g.count_indep(alpha + 1);
        bool naive_a = g.naive_has_k(alpha);
        bool naive_next = g.naive_has_k(alpha + 1);
        cout << "n=" << setw(2) << n
             << " | edges_G=" << setw(4) << g.edges_G
             << " | alpha=" << alpha
             << " | cnt(alpha)=" << setw(4) << c_alpha
             << " | cnt(alpha+1)=" << c_next
             << " | naive=(" << naive_a << "," << naive_next << ")"
             << " | wit_ok=" << wit_ok << endl;
        if (!wit_ok || c_next != 0 || c_alpha == 0 || !naive_a || naive_next) {
            cerr << "SELF-TEST FAILED on n=" << n << endl;
            exit(1);
        }
    }
}

void run_k7_attack(int sec_per_cfg, const string& out_path) {
    cout << "=== K=7 FRONTIER ATTACK (n in 52..57, target alpha <= 7) ===" << endl;
    ofstream fout(out_path);
    vector<vector<int64_t>> base_seeds;
    vector<int64_t> A53 = {-54,-34,-32,-30,-28,-26,-24,-22,-20,-18,-16,-15,-14,-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,22,24,26,28,30,32,34,54};
    vector<int64_t> A55 = {-84,-52,-48,-44,-40,-36,-32,-28,-26,-24,-22,-20,-18,-16,-15,-14,-12,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,22,24,26,28,32,36,40,44,48,52,84};
    base_seeds.push_back(A55);
    base_seeds.push_back(A53);
    base_seeds.push_back(KNOWN_WITNESSES.at(51));
    base_seeds.push_back(KNOWN_WITNESSES.at(43));

    vector<int64_t> singer57 = {0, 1, 3, 13, 32, 36, 43, 52};
    vector<int64_t> singer_comp;
    for (int x = 0; x < 57; ++x) {
        if (find(singer57.begin(), singer57.end(), x) == singer57.end())
            singer_comp.push_back(x - 28);
    }
    base_seeds.push_back(singer_comp);

    // Exhaustive immediate neighborhood around A55 (and A53)
    {
        TinySet sA;
        Graph128 g;
        cout << "--- Exhaustive 1-del / 1-add / sym-pair check around A55 ---" << endl;
        for (int i = 0; i < (int)A55.size(); ++i) {
            vector<int64_t> cand;
            for (int j = 0; j < (int)A55.size(); ++j) if (j != i) cand.push_back(A55[j]);
            g.build(cand, sA, 2);
            if (!g.has_indep_ge(8)) {
                cout << "  DEL from A55 (removed " << A55[i] << ") gives n=54 with alpha <= 7!" << endl;
                base_seeds.push_back(cand);
                break;
            }
        }
        for (int64_t x = -300; x <= 300; ++x) {
            if (binary_search(A55.begin(), A55.end(), x)) continue;
            vector<int64_t> cand = A55;
            cand.push_back(x);
            sort(cand.begin(), cand.end());
            g.build(cand, sA, 2);
            if (!g.has_indep_ge(8)) {
                cout << "  ADD " << x << " to A55 gives n=56 with alpha <= 7!" << endl;
                base_seeds.push_back(cand);
                break;
            }
        }
        for (int64_t x = 1; x <= 300; ++x) {
            if (binary_search(A55.begin(), A55.end(), x)) continue;
            vector<int64_t> cand = A55;
            cand.push_back(-x);
            cand.push_back(x);
            sort(cand.begin(), cand.end());
            g.build(cand, sA, 2);
            if (!g.has_indep_ge(8)) {
                cout << "  SYM-ADD +-" << x << " to A55 gives n=57 with alpha <= 7!" << endl;
                base_seeds.push_back(cand);
                break;
            }
        }
    }

    for (int n : {52, 53, 54, 55, 56, 57, 58}) {
        int best_alpha_n = 999;
        uint64_t best_cnt_n = UINT64_MAX;
        vector<int64_t> best_A_n;
        string best_cfg_n;

        vector<pair<int, int64_t>> configs;
        if (n % 2 == 1) {
            configs.push_back({1, 120});
            configs.push_back({1, 200});
            configs.push_back({1, 300});
        }
        configs.push_back({2, 120}); // asymmetric with 0 fixed
        configs.push_back({2, 220});
        configs.push_back({0, 120}); // fully asymmetric
        configs.push_back({0, 250});

        for (auto [mode, U] : configs) {
            SearchConfig cfg;
            cfg.n = n;
            cfg.target_alpha = 7;
            cfg.mode = mode;
            cfg.U = U;
            cfg.seconds = sec_per_cfg;
            cfg.count_cap = 20000;
            cfg.max_samples = 128;
            cfg.seed_rng = (uint64_t)(n * 1000 + mode * 100 + U);
            cfg.quiet = true;

            auto res = run_sa_search(cfg, base_seeds);
            cout << "  n=" << n << " mode=" << mode << " U=" << setw(3) << U
                 << " -> best_alpha=" << res.best_alpha
                 << " best_cnt=" << res.best_count << endl;
            if (res.best_alpha < best_alpha_n ||
                (res.best_alpha == best_alpha_n && res.best_count < best_cnt_n)) {
                best_alpha_n = res.best_alpha;
                best_cnt_n = res.best_count;
                best_A_n = res.best_A;
                best_cfg_n = "mode=" + to_string(mode) + "_U=" + to_string(U);
                if (!best_A_n.empty()) base_seeds.push_back(best_A_n);
            }
            if (res.found_target) {
                cout << "  *** BREAKTHROUGH! FOUND n=" << n << " WITH ALPHA <= 7! ***" << endl;
                break;
            }
        }

        fout << n << " " << best_alpha_n << " " << best_cnt_n << " " << best_cfg_n;
        for (int64_t x : best_A_n) fout << " " << x;
        fout << "\n";
        fout.flush();
    }
}

void run_batch_optimize(const string& seed_file, const string& out_file, int sec_per_n) {
    cout << "=== Batch Optimization for n in [52, 100] ===" << endl;
    map<int, int> best_alpha;
    map<int, vector<int64_t>> best_A;
    map<int, string> best_method;

    // Load sweep results
    {
        ifstream fin(seed_file);
        string line;
        while (getline(fin, line)) {
            if (line.empty()) continue;
            istringstream iss(line);
            int n, a;
            string m;
            iss >> n >> a >> m;
            vector<int64_t> A;
            int64_t v;
            while (iss >> v) A.push_back(v);
            normalize_set(A);
            if ((int)A.size() == n) {
                best_alpha[n] = a;
                best_A[n] = A;
                best_method[n] = m;
            }
        }
    }

    TinySet sA;
    // Propagate deletions/additions before SA
    for (int pass = 0; pass < 2; ++pass) {
        for (int n = 100; n >= 53; --n) {
            if (!best_A.count(n)) continue;
            // Try removing each element to form n-1
            const auto& cur = best_A[n];
            int best_sub_a = best_alpha.count(n - 1) ? best_alpha[n - 1] : 999;
            vector<int64_t> best_sub_A;
            #pragma omp parallel
            {
                TinySet lsA;
                Graph128 lg;
                #pragma omp for schedule(dynamic, 4)
                for (int rem = 0; rem < n; ++rem) {
                    vector<int64_t> cand;
                    cand.reserve(n - 1);
                    for (int j = 0; j < n; ++j) if (j != rem) cand.push_back(cur[j]);
                    lg.build(cand, lsA, 2);
                    int cur_b;
                    #pragma omp atomic read
                    cur_b = best_sub_a;
                    if (cur_b < 999 && lg.has_indep_ge(cur_b)) continue;
                    int a = lg.exact_alpha();
                    #pragma omp critical
                    {
                        if (a < best_sub_a) {
                            best_sub_a = a;
                            best_sub_A = cand;
                        }
                    }
                }
            }
            if (!best_sub_A.empty()) {
                best_alpha[n - 1] = best_sub_a;
                best_A[n - 1] = best_sub_A;
                best_method[n - 1] = "del_from_" + to_string(n);
            }
        }
    }

    // Now run targeted SA optimization for every n in [52, 100]
    // Order: milestones first or sweep 52..100
    for (int n = 52; n <= 100; ++n) {
        vector<vector<int64_t>> seeds;
        if (best_A.count(n)) seeds.push_back(best_A[n]);
        if (best_A.count(n - 1)) seeds.push_back(best_A[n - 1]);
        if (best_A.count(n + 1)) seeds.push_back(best_A[n + 1]);
        seeds.push_back(KNOWN_WITNESSES.at(51));

        int cur_a = best_alpha.count(n) ? best_alpha[n] : 999;
        int64_t max_abs = 60;
        if (best_A.count(n)) {
            for (int64_t x : best_A[n]) max_abs = max(max_abs, llabs(x));
        }
        int64_t U = min<int64_t>(max<int64_t>(2 * n, max_abs + 40), 2500);

        // Try symmetric and asymmetric around U, plus compact U = 2*n
        int target = max(7, cur_a - 1);
        for (int pass = 0; pass < 2; ++pass) {
            int mode = (pass == 0) ? 1 : 0; // sym then asym
            int64_t curU = (pass == 0) ? min<int64_t>(U, 400) : min<int64_t>(U, 300);
            // Wait: if best_A[n] is a glued witness with elements up to 66000, keep a large-U run too!
            if (pass == 1 && max_abs > 400) curU = max_abs + 200;

            SearchConfig cfg;
            cfg.n = n;
            cfg.target_alpha = target;
            cfg.mode = mode;
            cfg.U = curU;
            cfg.seconds = max(1, sec_per_n / 2);
            cfg.count_cap = 2048;
            cfg.max_samples = 64;
            cfg.seed_rng = (uint64_t)(n * 997 + pass * 31337);
            cfg.quiet = true;

            auto res = run_sa_search(cfg, seeds);
            if (res.best_alpha < cur_a) {
                cur_a = res.best_alpha;
                best_alpha[n] = cur_a;
                best_A[n] = res.best_A;
                best_method[n] = "sa_m" + to_string(mode) + "_U" + to_string(curU);
                seeds.insert(seeds.begin(), res.best_A);
                target = max(7, cur_a - 1);
            }
        }
        cout << "  OPT n=" << setw(3) << n << " | best_alpha=" << setw(2) << best_alpha[n]
             << " | method=" << best_method[n] << endl;
    }

    // Second downward propagation pass in case SA improved some n
    for (int n = 100; n >= 53; --n) {
        if (!best_A.count(n)) continue;
        const auto& cur = best_A[n];
        int best_sub_a = best_alpha.count(n - 1) ? best_alpha[n - 1] : 999;
        vector<int64_t> best_sub_A;
        #pragma omp parallel
        {
            TinySet lsA;
            Graph128 lg;
            #pragma omp for schedule(dynamic, 4)
            for (int rem = 0; rem < n; ++rem) {
                vector<int64_t> cand;
                cand.reserve(n - 1);
                for (int j = 0; j < n; ++j) if (j != rem) cand.push_back(cur[j]);
                lg.build(cand, lsA, 2);
                int cur_b;
                #pragma omp atomic read
                cur_b = best_sub_a;
                if (cur_b < 999 && lg.has_indep_ge(cur_b)) continue;
                int a = lg.exact_alpha();
                #pragma omp critical
                {
                    if (a < best_sub_a) {
                        best_sub_a = a;
                        best_sub_A = cand;
                    }
                }
            }
        }
        if (!best_sub_A.empty()) {
            best_alpha[n - 1] = best_sub_a;
            best_A[n - 1] = best_sub_A;
            best_method[n - 1] = "del2_from_" + to_string(n);
            cout << "  PROPAGATED n=" << setw(3) << n - 1 << " -> alpha=" << best_sub_a << endl;
        }
    }

    ofstream fout(out_file);
    for (int n = 52; n <= 100; ++n) {
        if (!best_A.count(n)) continue;
        // Final exact verification
        Graph128 g;
        g.build(best_A[n], sA, 2);
        vector<int64_t> wit;
        int exact_a = g.exact_alpha(&wit);
        if (exact_a != best_alpha[n] || !verify_witness_indep(best_A[n], wit)) {
            cerr << "VERIFICATION MISMATCH at n=" << n << endl;
            exit(1);
        }
        fout << n << " " << exact_a << " " << g.edges_G << " " << best_method[n];
        for (int64_t x : best_A[n]) fout << " " << x;
        fout << "\n";
    }
}

void verify_file(const string& path) {
    cout << "=== Exact Independent Verification of " << path << " ===" << endl;
    ifstream fin(path);
    string line;
    TinySet sA;
    int verified = 0;
    while (getline(fin, line)) {
        if (line.empty()) continue;
        istringstream iss(line);
        int n, claimed_a, claimed_edges;
        string method;
        iss >> n >> claimed_a >> claimed_edges >> method;
        vector<int64_t> A;
        int64_t v;
        while (iss >> v) A.push_back(v);
        vector<int64_t> orig = A;
        normalize_set(A);
        if ((int)A.size() != n || A != orig) {
            cerr << "FAIL: invalid/duplicate/unsorted elements at n=" << n << endl;
            exit(1);
        }
        Graph128 g2, g0;
        g2.build(A, sA, 2);
        g0.build(A, sA, 0);
        vector<int64_t> wit;
        int a2 = g2.exact_alpha(&wit);
        bool has_next = g0.has_indep_ge(a2 + 1);
        bool wit_ok = verify_witness_indep(A, wit) && ((int)wit.size() == a2);
        if (a2 != claimed_a || g2.edges_G != claimed_edges || has_next || !wit_ok) {
            cerr << "FAIL at n=" << n << ": claimed=" << claimed_a << " got=" << a2
                 << " has_next=" << has_next << " wit_ok=" << wit_ok << endl;
            exit(1);
        }
        verified++;
    }
    cout << "ALL " << verified << " WITNESS SETS 100% VERIFIED BY DUAL EXACT CHECK!" << endl;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        cout << "Usage:\n"
             << "  frontier_search selftest\n"
             << "  frontier_search check <elements...>\n"
             << "  frontier_search sweep <n_min> <n_max> <out_txt>\n"
             << "  frontier_search k7_attack <sec_per_cfg> <out_txt>\n"
             << "  frontier_search batch_opt <seed_txt> <out_txt> <sec_per_n>\n"
             << "  frontier_search verify_file <witness_txt>\n"
             << "  frontier_search search <n> <target_alpha> <mode> <U> <seconds> [seed_file]\n";
        return 0;
    }
    string cmd = argv[1];
    if (cmd == "selftest") {
        run_selftest();
    } else if (cmd == "check") {
        vector<int64_t> A;
        for (int i = 2; i < argc; ++i) A.push_back(stoll(argv[i]));
        normalize_set(A);
        TinySet sA;
        Graph128 g;
        g.build(A, sA, 2);
        vector<int64_t> wit;
        int alpha = g.exact_alpha(&wit);
        cout << "n=" << A.size() << " edges_G=" << g.edges_G << " alpha=" << alpha << endl;
        cout << "witness:";
        for (int64_t x : wit) cout << " " << x;
        cout << endl;
        cout << "witness_valid=" << verify_witness_indep(A, wit) << endl;
        if (alpha <= 12) {
            cout << "cnt(alpha)=" << g.count_indep(alpha) << " cnt(alpha+1)=" << g.count_indep(alpha + 1) << endl;
        }
    } else if (cmd == "sweep") {
        int n_min = stoi(argv[2]);
        int n_max = stoi(argv[3]);
        string out_path = argv[4];
        run_algebraic_sweep(n_min, n_max, out_path);
    } else if (cmd == "k7_attack") {
        int sec_per_cfg = stoi(argv[2]);
        string out_path = argv[3];
        run_k7_attack(sec_per_cfg, out_path);
    } else if (cmd == "batch_opt") {
        string seed_file = argv[2];
        string out_file = argv[3];
        int sec_per_n = stoi(argv[4]);
        run_batch_optimize(seed_file, out_file, sec_per_n);
    } else if (cmd == "verify_file") {
        verify_file(argv[2]);
    } else if (cmd == "search") {
        SearchConfig cfg;
        cfg.n = stoi(argv[2]);
        cfg.target_alpha = stoi(argv[3]);
        cfg.mode = stoi(argv[4]);
        cfg.U = stoll(argv[5]);
        cfg.seconds = stoi(argv[6]);
        vector<vector<int64_t>> seeds;
        if (argc >= 8) {
            ifstream fin(argv[7]);
            string line;
            while (getline(fin, line)) {
                istringstream iss(line);
                vector<int64_t> s;
                int64_t v;
                while (iss >> v) s.push_back(v);
                if (!s.empty()) seeds.push_back(s);
            }
        }
        if (seeds.empty()) {
            seeds.push_back(KNOWN_WITNESSES.at(51));
            seeds.push_back(KNOWN_WITNESSES.at(43));
            seeds.push_back(KNOWN_WITNESSES.at(31));
        }
        auto res = run_sa_search(cfg, seeds);
        cout << "\nFINAL_RESULT n=" << cfg.n << " target=" << cfg.target_alpha
             << " found=" << res.found_target << " best_alpha=" << res.best_alpha
             << " best_cnt=" << res.best_count << endl;
        cout << "SET:";
        for (int64_t x : res.best_A) cout << " " << x;
        cout << endl;
    }
    return 0;
}
