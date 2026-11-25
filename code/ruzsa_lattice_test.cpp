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
                         std::vector<int64_t>& cur, std::vector<Vec>& out) {
    if (idx == d) {
        out.push_back({cur});
        return;
    }
    int64_t maxd = static_cast<int64_t>(std::floor(std::sqrt((double)rem)));
    for (int64_t delta = -maxd; delta <= maxd; ++delta) {
        cur[idx] = c[idx] + delta;
        gen_ball_rec(idx + 1, d, rem - delta * delta, c, cur, out);
    }
}

static std::vector<Vec> gen_ball(int d, int64_t r, const std::vector<int64_t>& c) {
    std::vector<Vec> out;
    std::vector<int64_t> cur(d);
    gen_ball_rec(0, d, r, c, cur, out);
    return out;
}

// Fast count of lattice ball |B_s(0)| via dynamic programming: count[k] = # vectors with normSq == k
static std::vector<uint64_t> ball_counts_dp(int d, int max_r, bool checkerboard_D_d = false) {
    // Wait: if checkerboard_D_d, sum(x_j) must be even! Track parity [2][max_r+1]
    std::vector<std::vector<uint64_t>> dp(2, std::vector<uint64_t>(max_r + 1, 0));
    dp[0][0] = 1;
    for (int dim = 0; dim < d; ++dim) {
        std::vector<std::vector<uint64_t>> ndp(2, std::vector<uint64_t>(max_r + 1, 0));
        int maxv = (int)std::floor(std::sqrt((double)max_r));
        for (int v = -maxv; v <= maxv; ++v) {
            int sq = v * v;
            int par = (v & 1);
            for (int p = 0; p < 2; ++p) {
                for (int r = 0; r + sq <= max_r; ++r) {
                    ndp[p ^ par][r + sq] += dp[p][r];
                }
            }
        }
        dp = std::move(ndp);
    }
    std::vector<uint64_t> pref(max_r + 1, 0);
    uint64_t run = 0;
    for (int r = 0; r <= max_r; ++r) {
        run += dp[0][r];
        if (!checkerboard_D_d) run += dp[1][r];
        pref[r] = run;
    }
    return pref;
}

// Tomita MCQ color-bound exact max clique in complement (= max indep set in conflict graph)
static int best_indep = 0;
static void color_sort(const std::vector<std::vector<uint64_t>>& adj, const std::vector<int>& R,
                       std::vector<int>& order, std::vector<int>& colors, int words) {
    int m = (int)R.size();
    std::vector<std::vector<uint64_t>> csets;
    order.clear();
    colors.clear();
    // Simple greedy sequential coloring in complement
    for (int v : R) {
        int c = 0;
        while (c < (int)csets.size()) {
            bool conflict = false;
            for (int w = 0; w < words; ++w) {
                if (csets[c][w] & adj[v][w]) { conflict = true; break; }
            }
            if (!conflict) break;
            ++c;
        }
        if (c == (int)csets.size()) csets.emplace_back(words, 0);
        csets[c][v / 64] |= (1ULL << (v % 64));
    }
    for (int c = 0; c < (int)csets.size(); ++c) {
        for (int v : R) {
            if (csets[c][v / 64] & (1ULL << (v % 64))) {
                order.push_back(v);
                colors.push_back(c + 1);
            }
        }
    }
}

static void expand(const std::vector<std::vector<uint64_t>>& adj, std::vector<int> R, int cur, int words) {
    std::vector<int> order, colors;
    color_sort(adj, R, order, colors, words);
    while (!order.empty()) {
        int p = order.back();
        int col = colors.back();
        order.pop_back();
        colors.pop_back();
        if (cur + col <= best_indep) return;
        std::vector<int> Rp;
        for (int u : order) {
            if (adj[p][u / 64] & (1ULL << (u % 64))) Rp.push_back(u);
        }
        if (!Rp.empty()) {
            expand(adj, std::move(Rp), cur + 1, words);
        } else if (cur + 1 > best_indep) {
            best_indep = cur + 1;
        }
    }
}

int exact_alpha(const std::vector<Vec>& pts) {
    int n = (int)pts.size();
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
    std::vector<int> R(n);
    for (int i = 0; i < n; ++i) R[i] = i;
    best_indep = 0;
    expand(comp, R, 0, words);
    return best_indep;
}

int main() {
    std::cout << "=== 1. Rigorous Crossover vs k^2+3k-11: Z^d vs D_d Multi-Scale Balls ===\n" << std::flush;
    for (int d : {3, 4, 5, 6, 8}) {
        std::cout << "\n--- Dimension d = " << d << " (Z^d step=1 vs D_d step=2) ---\n";
        int max_r = (d <= 4 ? 1200 : (d <= 6 ? 300 : 120));
        auto cntZ = ball_counts_dp(d, max_r, false);
        auto cntD = ball_counts_dp(d, max_r, true);

        // Z^d construction with A = U_{i=0}^{L-1} 2^i B_{L-i}(c) plus 2^L B_0(c) = {2^L c}
        //Wait: WITH 2^L B_0(c), layer L-1 has pairs in B_1(c) sum to 2c in B_0(c), so |S_{L-1}| <= d!
        // Thus k <= (L - 1) * 2^d + d + 1 (since c in B_0 gives 1 more element, wait 2^L c itself + at most d from B_1)
        uint64_t prefZ = 0, firstZ_k = 0, firstZ_n = 0;
        for (int L = 1; L <= max_r; ++L) {
            prefZ += cntZ[L];
            uint64_t n = prefZ + 1; // +1 for 2^L * c
            uint64_t k = (uint64_t)(L - 1) * (1ULL << d) + (d + 1);
            uint64_t quad = k * k + 3 * k - 11;
            if (n > quad && firstZ_k == 0) {
                firstZ_k = k; firstZ_n = n;
                std::cout << "  [Z^d FIRST BEATS k^2+3k-11] L=" << L << " k<=" << k
                          << " n=" << n << " (quad=" << quad << ")\n";
                break;
            }
        }
        if (firstZ_k == 0) {
            uint64_t k = (uint64_t)(max_r - 1) * (1ULL << d) + (d + 1);
            std::cout << "  [Z^d] up to L=" << max_r << " ratio=" << (double)(prefZ+1)/(double)(k*k+3*k-11) << "\n";
        }

        // D_d construction: A = U_{i=0}^{L-1} 2^i (B_{2(L-i)}(c) cap D_d) + {2^L c}
        // Step in normSq is 2!! And |D_d / 2D_d| = 2^d!
        // Layer i=L-1 has normSq <= 2 in D_d: 1 (zero) + 2*d*(d-1) roots (±1,±1,0..)!
        uint64_t prefD = 0, firstD_k = 0, firstD_n = 0;
        for (int L = 1; 2 * L <= max_r; ++L) {
            prefD += cntD[2 * L];
            uint64_t n = prefD + 1;
            uint64_t k = (uint64_t)L * (1ULL << d) + 1;
            uint64_t quad = k * k + 3 * k - 11;
            if (n > quad && firstD_k == 0) {
                firstD_k = k; firstD_n = n;
                std::cout << "  [D_d FIRST BEATS k^2+3k-11] L=" << L << " k<=" << k
                          << " n=" << n << " (quad=" << quad << ")\n";
                break;
            }
        }
    }

    std::cout << "\n=== 2. Exact alpha(G_A) on Small 2-adic Ball Families ===\n" << std::flush;
    for (int d : {2, 3}) {
        std::vector<int64_t> c_pos(d, 100);
        for (int r = 1; r <= (d == 2 ? 6 : 4); ++r) {
            std::vector<Vec> A_shift;
            std::vector<int64_t> zero_c(d, 0);
            for (int i = 0; i < r; ++i) {
                auto b = gen_ball(d, r - i, zero_c);
                int64_t sc = 1LL << i;
                for (auto v : b) {
                    Vec u; u.x.resize(d);
                    for (int t = 0; t < d; ++t) u.x[t] = sc * (c_pos[t] + v.x[t]);
                    A_shift.push_back(u);
                }
            }
            // Add 2^r * c_pos!
            Vec top; top.x.resize(d);
            for (int t = 0; t < d; ++t) top.x[t] = (1LL << r) * c_pos[t];
            A_shift.push_back(top);
            int alpha = exact_alpha(A_shift);
            uint64_t k_bound = (uint64_t)(r - 1) * (1ULL << d) + d + 1;
            std::cout << "d=" << d << " r=" << r << " n=" << A_shift.size()
                      << " EXACT alpha=" << alpha << " (upper bound=" << k_bound
                      << ", quad(exact)=" << (alpha*alpha + 3*alpha - 11) << ")\n" << std::flush;
        }
    }
    return 0;
}
