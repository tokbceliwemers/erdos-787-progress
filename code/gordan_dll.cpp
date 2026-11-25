#include <algorithm>
#include <cmath>
#include <cstdint>
#include <numeric>
#include <vector>

using namespace std;

struct Triple {
    int i, j, l;
};

static bool verify_integer_core(int m, const vector<Triple>& eqs, const vector<int>& sub,
                                const vector<int64_t>& Y) {
    __int128 col_sum[64];
    for (int t = 0; t < m; ++t) col_sum[t] = 0;
    for (size_t idx = 0; idx < sub.size(); ++idx) {
        int64_t y = Y[idx];
        if (y == 0) continue;
        const Triple& tr = eqs[sub[idx]];
        for (int t = 0; t <= tr.i; ++t) col_sum[t] += y;
        for (int t = tr.j + 1; t <= tr.l; ++t) col_sum[t] -= y;
    }
    __int128 total = 0;
    for (int t = 0; t < m; ++t) {
        if (col_sum[t] < 0) return false;
        total += col_sum[t];
    }
    return total > 0;
}

static bool try_extract_exact_Y(int m, const vector<Triple>& eqs, const vector<int>& sub,
                                const vector<long double>& y_ld, vector<int64_t>& out_Y) {
    int r = (int)sub.size();
    long double max_abs = 0;
    for (int q = 0; q < r; ++q) max_abs = max(max_abs, fabsl(y_ld[q]));
    if (max_abs < 1e-12L) return false;

    vector<long double> yn(r);
    for (int q = 0; q < r; ++q) yn[q] = -y_ld[q] / max_abs;

    out_Y.resize(r);
    static const int64_t scales[] = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 60, 120, 360, 720, 2520};
    for (int64_t S : scales) {
        for (int q = 0; q < r; ++q) out_Y[q] = llround(yn[q] * (long double)S);
        if (verify_integer_core(m, eqs, sub, out_Y)) return true;
    }

    auto approx_frac = [](long double x, int64_t max_den, int64_t& num, int64_t& den) {
        int sgn = (x < 0) ? -1 : 1;
        long double ax = fabsl(x);
        if (ax < 1e-13L) { num = 0; den = 1; return; }
        int64_t p0 = 0, q0 = 1, p1 = 1, q1 = 0;
        long double rem = ax;
        for (int it = 0; it < 40; ++it) {
            int64_t a = (int64_t)floorl(rem + 1e-14L);
            if (q1 > 0 && a > (max_den - q0) / q1) {
                int64_t k = (max_den - q0) / q1;
                if (k > 0) {
                    p1 = p0 + k * p1;
                    q1 = q0 + k * q1;
                }
                break;
            }
            int64_t p2 = p0 + a * p1;
            int64_t q2 = q0 + a * q1;
            p0 = p1; q0 = q1;
            p1 = p2; q1 = q2;
            long double frac = rem - (long double)a;
            if (frac < 1e-12L || q1 >= max_den) break;
            rem = 1.0L / frac;
        }
        num = sgn * p1;
        den = q1;
    };

    vector<int64_t> nums(r), dens(r);
    __int128 common = 1;
    for (int q = 0; q < r; ++q) {
        approx_frac(yn[q], 100000, nums[q], dens[q]);
        if (nums[q] != 0) {
            int64_t g = std::gcd((int64_t)common, dens[q]);
            common = (common / g) * dens[q];
            if (common > 1000000000000LL) return false;
        }
    }
    for (int q = 0; q < r; ++q) {
        out_Y[q] = (int64_t)((__int128)nums[q] * (common / dens[q]));
    }
    return verify_integer_core(m, eqs, sub, out_Y);
}

static int simplex_gordan(int m, const vector<Triple>& eqs, const vector<int>& sub,
                          vector<long double>& y_out) {
    int r = (int)sub.size();
    if (r == 0) return 1;
    int cols = m + r + 1;
    int rows = r + 1;

    vector<long double> T(rows * cols, 0.0L);
    vector<int> row_sign(r, 1);
    vector<int> basis(r);

    auto at = [&](int row, int col) -> long double& { return T[row * cols + col]; };

    for (int q = 0; q < r; ++q) {
        const Triple& tr = eqs[sub[q]];
        long double b_val = -(long double)((tr.i + 1) - (tr.l - tr.j));
        int sgn = (b_val < 0.0L) ? -1 : 1;
        row_sign[q] = sgn;
        for (int t = 0; t <= tr.i; ++t) at(q, t) = (long double)sgn;
        for (int t = tr.j + 1; t <= tr.l; ++t) at(q, t) = -(long double)sgn;
        at(q, m + q) = 1.0L;
        at(q, m + r) = (long double)sgn * b_val;
        basis[q] = m + q;
    }

    for (int q = 0; q < r; ++q) {
        for (int j = 0; j < m; ++j) at(r, j) += at(q, j);
        at(r, m + r) += at(q, m + r);
    }

    int max_pivots = 4000;
    for (int piv = 0; piv < max_pivots; ++piv) {
        int enter = -1;
        for (int j = 0; j < m + r; ++j) {
            if (at(r, j) > 1e-11L) {
                enter = j;
                break;
            }
        }
        if (enter == -1) {
            long double w_star = at(r, m + r);
            if (w_star > 1e-8L) {
                y_out.resize(r);
                for (int q = 0; q < r; ++q) {
                    long double dbar = -at(r, m + q);
                    long double ytilde = 1.0L - dbar;
                    y_out[q] = (long double)row_sign[q] * ytilde;
                }
                return 0;
            }
            return 1;
        }

        int leave = -1;
        long double best_ratio = 1e100L;
        for (int q = 0; q < r; ++q) {
            long double a_qe = at(q, enter);
            if (a_qe > 1e-11L) {
                long double ratio = at(q, m + r) / a_qe;
                if (ratio < 0.0L) ratio = 0.0L;
                if (leave == -1 || ratio < best_ratio - 1e-13L ||
                    (fabsl(ratio - best_ratio) <= 1e-13L && basis[q] < basis[leave])) {
                    best_ratio = ratio;
                    leave = q;
                }
            }
        }
        if (leave == -1) return -1;

        long double pval = at(leave, enter);
        long double inv = 1.0L / pval;
        for (int j = 0; j <= m + r; ++j) at(leave, j) *= inv;
        at(leave, enter) = 1.0L;
        for (int i = 0; i <= r; ++i) {
            if (i == leave) continue;
            long double factor = at(i, enter);
            if (fabsl(factor) <= 1e-16L) continue;
            for (int j = 0; j <= m + r; ++j) {
                at(i, j) -= factor * at(leave, j);
            }
            at(i, enter) = 0.0L;
        }
        basis[leave] = enter;
    }
    return -1;
}

extern "C" {
__declspec(dllexport) int find_minimal_core(int m, int r, const int* triples_flat, int* out_core_indices) {
    if (r <= 0 || m <= 0 || m > 64) return 0;
    vector<Triple> eqs(r);
    vector<int> active(r);
    for (int q = 0; q < r; ++q) {
        eqs[q] = {triples_flat[3 * q], triples_flat[3 * q + 1], triples_flat[3 * q + 2]};
        active[q] = q;
    }
    vector<long double> y;
    int st = simplex_gordan(m, eqs, active, y);
    if (st != 0) return 0;

    vector<pair<long double, int>> nonzero;
    for (int i = 0; i < r; ++i) {
        if (fabsl(y[i]) > 1e-9L) nonzero.push_back({fabsl(y[i]), i});
    }
    sort(nonzero.begin(), nonzero.end());
    vector<int> cur;
    cur.reserve(nonzero.size());
    for (auto& kv : nonzero) cur.push_back(kv.second);
    if (cur.empty()) cur = active;

    for (size_t pos = 0; pos < cur.size(); ) {
        if (cur.size() <= 2) break;
        vector<int> trial;
        trial.reserve(cur.size() - 1);
        for (size_t j = 0; j < cur.size(); ++j) {
            if (j != pos) trial.push_back(cur[j]);
        }
        vector<long double> yt;
        vector<int64_t> Yt;
        if (simplex_gordan(m, eqs, trial, yt) == 0 && try_extract_exact_Y(m, eqs, trial, yt, Yt)) {
            cur = std::move(trial);
            continue;
        }
        ++pos;
    }

    vector<long double> y_fin;
    vector<int64_t> Y_fin;
    if (simplex_gordan(m, eqs, cur, y_fin) == 0 && try_extract_exact_Y(m, eqs, cur, y_fin, Y_fin)) {
        for (size_t i = 0; i < cur.size(); ++i) out_core_indices[i] = cur[i];
        return (int)cur.size();
    }

    vector<int64_t> Y_raw;
    if (try_extract_exact_Y(m, eqs, active, y, Y_raw)) {
        int cnt = 0;
        for (int i = 0; i < r; ++i) {
            if (Y_raw[i] != 0) out_core_indices[cnt++] = i;
        }
        return cnt;
    }
    return 0;
}
}
