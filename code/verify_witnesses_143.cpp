#include <algorithm>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace std;

static constexpr int MAX_N = 192;

struct BitVec {
    uint64_t w[3] = {0, 0, 0};
    inline void set(int i) { w[i >> 6] |= (1ULL << (i & 63)); }
    inline void clr(int i) { w[i >> 6] &= ~(1ULL << (i & 63)); }
    inline bool any() const { return (w[0] | w[1] | w[2]) != 0; }
    inline int popcnt() const {
        return __builtin_popcountll(w[0]) + __builtin_popcountll(w[1]) + __builtin_popcountll(w[2]);
    }
    inline int ctz() const {
        if (w[0]) return __builtin_ctzll(w[0]);
        if (w[1]) return 64 + __builtin_ctzll(w[1]);
        return 128 + __builtin_ctzll(w[2]);
    }
    inline BitVec operator&(const BitVec& o) const {
        return {{w[0] & o.w[0], w[1] & o.w[1], w[2] & o.w[2]}};
    }
};

struct TinySet {
    static constexpr int CAP = 2048;
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

struct Graph192 {
    int n = 0;
    int64_t elements[MAX_N];
    BitVec adj_G[MAX_N], comp_adj[MAX_N];
    int edges_G = 0, best_alpha = 0, target_stop = 0;
    vector<int> best_wit_idx;

    void build(const vector<int64_t>& A, TinySet& sA, int order_mode) {
        n = (int)A.size();
        sA.clear();
        for (int i = 0; i < n; ++i) sA.insert(A[i]);
        int raw_deg[MAX_N] = {};
        edges_G = 0;
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                if (sA.contains(A[i] + A[j])) {
                    raw_deg[i]++;
                    raw_deg[j]++;
                    edges_G++;
                }
            }
        }
        int ord[MAX_N];
        for (int i = 0; i < n; ++i) ord[i] = i;
        if (order_mode == 2) {
            sort(ord, ord + n, [&](int a, int b) {
                if (raw_deg[a] != raw_deg[b]) return raw_deg[a] < raw_deg[b];
                return A[a] < A[b];
            });
        }
        for (int i = 0; i < n; ++i) {
            elements[i] = A[ord[i]];
            adj_G[i] = BitVec();
            comp_adj[i] = BitVec();
        }
        for (int i = 0; i < n; ++i) {
            int64_t u = elements[i];
            for (int j = i + 1; j < n; ++j) {
                if (sA.contains(u + elements[j])) {
                    adj_G[i].set(j);
                    adj_G[j].set(i);
                } else {
                    comp_adj[i].set(j);
                    comp_adj[j].set(i);
                }
            }
        }
    }

    BitVec full_mask() const {
        BitVec f;
        for (int i = 0; i < n; ++i) f.set(i);
        return f;
    }

    void expand(BitVec P, int depth, vector<int>& cur_idx) {
        if (!P.any()) {
            if (depth > best_alpha) {
                best_alpha = depth;
                best_wit_idx = cur_idx;
            }
            return;
        }
        if (depth + P.popcnt() <= best_alpha) return;
        int order[MAX_N], color[MAX_N], m = 0, c = 0;
        BitVec U = P;
        while (U.any()) {
            c++;
            BitVec Q = U;
            while (Q.any()) {
                int v = Q.ctz();
                order[m] = v;
                color[m] = c;
                m++;
                U.clr(v);
                Q.w[0] &= adj_G[v].w[0];
                Q.w[1] &= adj_G[v].w[1];
                Q.w[2] &= adj_G[v].w[2];
            }
        }
        if (depth + c <= best_alpha) return;
        for (int i = m - 1; i >= 0; --i) {
            if (depth + color[i] <= best_alpha) return;
            int v = order[i];
            P.clr(v);
            BitVec next_P = P & comp_adj[v];
            cur_idx.push_back(v);
            if (next_P.any()) {
                expand(next_P, depth + 1, cur_idx);
            } else if (depth + 1 > best_alpha) {
                best_alpha = depth + 1;
                best_wit_idx = cur_idx;
            }
            cur_idx.pop_back();
            if (target_stop > 0 && best_alpha >= target_stop) return;
        }
    }

    int exact_alpha(vector<int64_t>* out_wit = nullptr) {
        best_alpha = 0;
        target_stop = 0;
        best_wit_idx.clear();
        vector<int> cur_idx;
        if (n == 0) return 0;
        expand(full_mask(), 0, cur_idx);
        if (out_wit) {
            out_wit->clear();
            for (int idx : best_wit_idx) out_wit->push_back(elements[idx]);
        }
        return best_alpha;
    }

    bool has_indep_ge(int k) {
        if (k <= 0) return true;
        if (k > n) return false;
        best_alpha = k - 1;
        target_stop = k;
        best_wit_idx.clear();
        vector<int> cur_idx;
        expand(full_mask(), 0, cur_idx);
        return best_alpha >= k;
    }
};

static bool verify_witness_indep(const vector<int64_t>& A, const vector<int64_t>& B) {
    set<int64_t> sA(A.begin(), A.end());
    for (int64_t b : B) if (!sA.count(b)) return false;
    for (size_t i = 0; i < B.size(); ++i)
        for (size_t j = i + 1; j < B.size(); ++j)
            if (sA.count(B[i] + B[j])) return false;
    return true;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        cerr << "Usage: verify_witnesses_143 <witness_file> [check_edges=1]\n";
        return 1;
    }
    bool check_edges = (argc >= 3) ? (atoi(argv[2]) != 0) : true;
    ifstream fin(argv[1]);
    if (!fin) {
        cerr << "Failed to open " << argv[1] << "\n";
        return 1;
    }
    string line;
    int rows = 0;
    TinySet sA;
    Graph192 g0, g2;
    while (getline(fin, line)) {
        if (line.empty()) continue;
        istringstream iss(line);
        int n, alpha, col3;
        string tag;
        iss >> n >> alpha >> col3 >> tag;
        vector<int64_t> A;
        int64_t x;
        while (iss >> x) A.push_back(x);
        if ((int)A.size() != n || n > MAX_N) {
            cerr << "Size error at n=" << n << " got=" << A.size() << "\n";
            return 1;
        }
        set<int64_t> uniq(A.begin(), A.end());
        if ((int)uniq.size() != n) {
            cerr << "Duplicate elements at n=" << n << "\n";
            return 1;
        }
        g2.build(A, sA, 2);
        vector<int64_t> wit;
        int a2 = g2.exact_alpha(&wit);
        g0.build(A, sA, 0);
        if (a2 != alpha || (check_edges && g2.edges_G != col3) ||
            g0.has_indep_ge(alpha + 1) || !verify_witness_indep(A, wit) || (int)wit.size() != alpha) {
            cerr << "Verification failure at n=" << n << " a2=" << a2 << " exp=" << alpha << "\n";
            return 1;
        }
        rows++;
    }
    cout << "DUAL_VERIFIED file=" << argv[1] << " rows=" << rows << " PASS\n";
    return 0;
}
