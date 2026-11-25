#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <set>
#include <cstdint>

struct Vec {
    std::vector<int64_t> x;
    bool operator<(const Vec& o) const { return x < o.x; }
    bool operator==(const Vec& o) const { return x == o.x; }
};

static void gen_ball_rec(int idx, int d, int64_t rem, const std::vector<int64_t>& c,
                         std::vector<int64_t>& cur, std::vector<Vec>& out, bool D_d, int sum_par) {
    if (idx == d) {
        if (!D_d || (sum_par & 1) == 0) out.push_back({cur});
        return;
    }
    int64_t maxd = static_cast<int64_t>(std::floor(std::sqrt((double)rem)));
    for (int64_t delta = -maxd; delta <= maxd; ++delta) {
        cur[idx] = c[idx] + delta;
        gen_ball_rec(idx + 1, d, rem - delta * delta, c, cur, out, D_d, sum_par ^ (int)(std::abs(delta) & 1));
    }
}

static std::vector<Vec> gen_ball(int d, int64_t r, const std::vector<int64_t>& c, bool D_d = false) {
    std::vector<Vec> out;
    std::vector<int64_t> cur(d);
    gen_ball_rec(0, d, r, c, cur, out, D_d, 0);
    return out;
}

static int best_indep = 0;
static void color_sort(const std::vector<std::vector<uint64_t>>& adj, const std::vector<int>& R,
                       std::vector<int>& order, std::vector<int>& colors, int words) {
    std::vector<std::vector<uint64_t>> csets;
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
    for (int c = 0; c < (int)csets.size(); ++c) {
        for (int v : R) if (csets[c][v / 64] & (1ULL << (v % 64))) { order.push_back(v); colors.push_back(c + 1); }
    }
}

static void expand(const std::vector<std::vector<uint64_t>>& adj, std::vector<int> R, int cur, int words) {
    std::vector<int> order, colors;
    color_sort(adj, R, order, colors, words);
    while (!order.empty()) {
        int p = order.back(), col = colors.back();
        order.pop_back(); colors.pop_back();
        if (cur + col <= best_indep) return;
        std::vector<int> Rp;
        for (int u : order) if (adj[p][u / 64] & (1ULL << (u % 64))) Rp.push_back(u);
        if (!Rp.empty()) expand(adj, std::move(Rp), cur + 1, words);
        else if (cur + 1 > best_indep) best_indep = cur + 1;
    }
}

int exact_alpha(const std::vector<Vec>& pts) {
    int n = (int)pts.size();
    if (n == 0) return 0;
    std::set<Vec> S(pts.begin(), pts.end());
    int words = (n + 63) / 64;
    std::vector<std::vector<uint64_t>> comp(n, std::vector<uint64_t>(words, 0));
    int d = (int)pts[0].x.size();
    Vec sum; sum.x.resize(d);
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            for (int k = 0; k < d; ++k) sum.x[k] = pts[i].x[k] + pts[j].x[k];
            if (!S.count(sum)) {
                comp[i][j / 64] |= (1ULL << (j % 64));
                comp[j][i / 64] |= (1ULL << (i % 64));
            }
        }
    }
    std::vector<int> R(n); for (int i = 0; i < n; ++i) R[i] = i;
    best_indep = 0;
    expand(comp, R, 0, words);
    return best_indep;
}

bool lex_pos(const Vec& v) {
    for (int i = (int)v.x.size() - 1; i >= 0; --i) {
        if (v.x[i] > 0) return true;
        if (v.x[i] < 0) return false;
    }
    return false;
}

int main() {
    std::cout << "=== 1. D_d Shifted Verification (Exact alpha vs bound) ===\n" << std::flush;
    for (int d : {2, 3, 4}) {
        std::vector<int64_t> c_pos(d, 100);
        for (int L = 1; L <= (d == 2 ? 5 : (d == 3 ? 3 : 2)); ++L) {
            std::vector<Vec> A;
            std::vector<int64_t> zero_c(d, 0);
            for (int i = 0; i < L; ++i) {
                auto b = gen_ball(d, 2 * (L - i), zero_c, true);
                int64_t sc = 1LL << i;
                for (auto v : b) {
                    Vec u; u.x.resize(d);
                    for (int t = 0; t < d; ++t) u.x[t] = sc * (c_pos[t] + v.x[t]);
                    A.push_back(u);
                }
            }
            Vec top; top.x.resize(d);
            for (int t = 0; t < d; ++t) top.x[t] = (1LL << L) * c_pos[t];
            A.push_back(top);
            if (A.size() <= 140) {
                int alpha = exact_alpha(A);
                int bound = (L - 1) * (1 << d) + (d * (d - 1) + 2);
                int l2d = L * (1 << d);
                std::cout << "D_" << d << " L=" << L << " n=" << A.size()
                          << " EXACT alpha=" << alpha << " bound=" << bound
                          << " (L*2^d=" << l2d << ")\n" << std::flush;
                if (alpha > bound) {
                    std::cerr << "ERROR: D_" << d << " L=" << L << " alpha=" << alpha
                              << " exceeds bound=" << bound << "\n";
                    return 1;
                }
            }
        }
    }

    std::cout << "\n=== 2. Origin-Centered Z^d (Full & Positive Half A_+) ===\n" << std::flush;
    for (int d : {2, 3}) {
        std::vector<int64_t> zero_c(d, 0);
        for (int r = 1; r <= (d == 2 ? 6 : 4); ++r) {
            std::set<Vec> Aset;
            for (int i = 0; i < r; ++i) {
                auto b = gen_ball(d, r - i, zero_c, false);
                int64_t sc = 1LL << i;
                for (auto v : b) {
                    for (auto& coord : v.x) coord *= sc;
                    Aset.insert(v);
                }
            }
            std::vector<Vec> A(Aset.begin(), Aset.end());
            std::vector<Vec> Apos;
            for (auto& v : A) if (lex_pos(v)) Apos.push_back(v);
            if (A.size() <= 140) {
                int a_full = exact_alpha(A);
                int a_pos = exact_alpha(Apos);
                std::cout << "Zero-centered Z^" << d << " r=" << r
                          << " |A|=" << A.size() << " exact_alpha=" << a_full
                          << " |A_+|=" << Apos.size() << " exact_alpha(A_+)=" << a_pos << "\n" << std::flush;
            }
        }
    }
    return 0;
}
