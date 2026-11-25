#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>

using namespace std;

struct Vec {
    vector<int64_t> x;
    bool operator<(const Vec& o) const { return x < o.x; }
};

static void gen_ball_rec(int idx, int d, int64_t rem, vector<int64_t>& cur, vector<Vec>& out, bool D_d, int sum_par) {
    if (idx == d) {
        if (!D_d || (sum_par & 1) == 0) out.push_back({cur});
        return;
    }
    int64_t maxd = (int64_t)floor(sqrt((double)rem));
    for (int64_t delta = -maxd; delta <= maxd; ++delta) {
        cur[idx] = delta;
        gen_ball_rec(idx + 1, d, rem - delta * delta, cur, out, D_d, sum_par ^ (int)(llabs(delta) & 1));
    }
}

static int best_indep = 0;
static void color_sort(const vector<vector<uint64_t>>& adj, const vector<int>& R,
                       vector<int>& order, vector<int>& colors, int words) {
    vector<vector<uint64_t>> csets;
    order.clear(); colors.clear();
    for (int v : R) {
        int c = 0;
        while (c < (int)csets.size()) {
            bool conflict = false;
            for (int w = 0; w < words; ++w) if (csets[c][w] & adj[v][w]) { conflict = true; break; }
            if (!conflict) break;
            ++c;
        }
        if (c == (int)csets.size()) csets.emplace_back(words, 0);
        csets[c][v / 64] |= (1ULL << (v % 64));
    }
    for (int c = 0; c < (int)csets.size(); ++c)
        for (int v : R) if (csets[c][v / 64] & (1ULL << (v % 64))) { order.push_back(v); colors.push_back(c + 1); }
}

static void expand(const vector<vector<uint64_t>>& adj, vector<int> R, int cur, int words) {
    vector<int> order, colors;
    color_sort(adj, R, order, colors, words);
    while (!order.empty()) {
        int p = order.back(), col = colors.back();
        order.pop_back(); colors.pop_back();
        if (cur + col <= best_indep) return;
        vector<int> Rp;
        for (int u : order) if (adj[p][u / 64] & (1ULL << (u % 64))) Rp.push_back(u);
        if (!Rp.empty()) expand(adj, move(Rp), cur + 1, words);
        else if (cur + 1 > best_indep) best_indep = cur + 1;
    }
}

static int exact_alpha(const vector<Vec>& pts) {
    int n = (int)pts.size();
    set<Vec> S(pts.begin(), pts.end());
    int words = (n + 63) / 64;
    vector<vector<uint64_t>> comp(n, vector<uint64_t>(words, 0));
    int d = (int)pts[0].x.size();
    Vec sum; sum.x.resize(d);
    for (int i = 0; i < n; ++i) for (int j = i + 1; j < n; ++j) {
        for (int k = 0; k < d; ++k) sum.x[k] = pts[i].x[k] + pts[j].x[k];
        if (!S.count(sum)) { comp[i][j / 64] |= (1ULL << (j % 64)); comp[j][i / 64] |= (1ULL << (i % 64)); }
    }
    vector<int> R(n); for (int i = 0; i < n; ++i) R[i] = i;
    best_indep = 0; expand(comp, R, 0, words); return best_indep;
}

int main() {
    cout << "=== Zero-Centered Z^d vs Zero-Centered D_d ===" << endl;
    for (int d : {2, 3, 4}) {
        int maxL = (d == 2 ? 10 : (d == 3 ? 6 : 3));
        for (int L = 1; L <= maxL; ++L) {
            set<Vec> Aset;
            for (int i = 0; i < L; ++i) {
                vector<Vec> b; vector<int64_t> cur(d);
                gen_ball_rec(0, d, 2 * (L - i), cur, b, true, 0);
                int64_t sc = 1LL << i;
                for (auto v : b) { for (auto& x : v.x) x *= sc; Aset.insert(v); }
            }
            Vec zero_v; zero_v.x.assign(d, 0); Aset.insert(zero_v);
            vector<Vec> A(Aset.begin(), Aset.end());
            if ((int)A.size() <= 180) {
                int a = exact_alpha(A);
                cout << "Zero D_" << d << " L=" << L << " n=" << A.size() << " EXACT alpha=" << a << endl;
            }
        }
    }
    for (int L = 5; L <= 7; ++L) {
        int d = 3;
        set<Vec> Aset;
        for (int i = 0; i < L; ++i) {
            vector<Vec> b; vector<int64_t> cur(d);
            gen_ball_rec(0, d, L - i, cur, b, false, 0);
            int64_t sc = 1LL << i;
            for (auto v : b) { for (auto& x : v.x) x *= sc; Aset.insert(v); }
        }
        vector<Vec> A(Aset.begin(), Aset.end());
        if ((int)A.size() <= 180) {
            int a = exact_alpha(A);
            cout << "Zero Z_3 L=" << L << " n=" << A.size() << " EXACT alpha=" << a << endl;
        }
    }
    return 0;
}
