#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <omp.h>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using namespace std;

struct Triple {
    int i, j, l;
};

struct SolverTask {
    int m, k;
    int j_elim; // -1 for None
    int u_low;  // -1 for None
    int u_high; // -1 for None
};

// Exact Rational/Integer verification of a Gordan Farkas core:
// Checks if integer weights Y[0..r-1] satisfy (M_C^T Y)[t] >= 0 for all t=0..m-1
// and sum_t (M_C^T Y)[t] > 0 using 128-bit arithmetic.
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

    // Negate because Phase-I gives y^T M <= 0, we want M^T Y >= 0 => Y = -y.
    vector<long double> yn(r);
    for (int q = 0; q < r; ++q) yn[q] = -y_ld[q] / max_abs;

    out_Y.resize(r);
    static const int64_t scales[] = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 60, 120, 360, 720, 2520};
    for (int64_t S : scales) {
        for (int q = 0; q < r; ++q) out_Y[q] = llround(yn[q] * (long double)S);
        if (verify_integer_core(m, eqs, sub, out_Y)) return true;
    }

    // Continued fraction rationalization of each entry up to max_den = 100000
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

// Phase-I Simplex checking feasibility of M d = 0, d >= 1 (i.e. M u = -M * 1, u >= 0).
// Returns:
//   0 = infeasible (with y_out containing raw Farkas vector: (-y_out)^T M >= 0, sum > 0)
//   1 = feasible (M d = 0, d >= 1)
//  -1 = numerical edge / max pivots
static int simplex_gordan(int m, const vector<Triple>& eqs, const vector<int>& sub,
                          vector<long double>& y_out) {
    int r = (int)sub.size();
    if (r == 0) return 1;
    int cols = m + r + 1; // 0..m-1: u, m..m+r-1: art a, m+r: RHS
    int rows = r + 1;     // 0..r-1: constraints, r: objective w

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
        at(q, m + r) = (long double)sgn * b_val; // >= 0
        basis[q] = m + q;
    }

    // Objective row r: w = sum a_q => initially sum(a_q) - w = 0 => w + (-sum M_tilde) u = sum b_tilde
    // Reduced cost array stored in row r: T[r, j] = -coef_of_j_in_w_expr, wait:
    // Keep standard min tableau: row r represents w - sum_j (-rc_j) x_j = rhs, wait let's be crystal clear!
    // Store Z = sum_j c_j x_j with tableau row: w + sum_j T[r, j] * x_j = T[r, rhs]
    // Meaning w = T[r, rhs] - sum_j T[r, j] * x_j.
    // Wait: to MINIMIZE w, increasing x_j increases w by -T[r, j], so we enter j with T[r, j] > 0!
    // Initially w = sum a_q = sum (b_q - sum M_qt u_t) => w + sum_t (sum_q M_qt) u_t = sum_q b_q.
    // Check: if u_t increases from 0, w decreases if sum_q M_qt > 0, i.e., T[r, t] > 0!
    // And when eliminating a_q in T[r, m+q]: initially a_q has coeff 1 in w, and is eliminated using
    // constraint row q, so T[r, m+q] starts at 0!
    // After elimination/pivoting:
    //   w = rhs - sum_j T[r, j] * x_j = rhs + sum_j (-T[r, j]) * x_j.
    // Optimal (minimum) occurs when T[r, j] <= 1e-11 for ALL non-basic j!
    // At optimality: w* = T[r, rhs], and w = sum a_q = w* + sum_j (-T[r, j]) x_j.
    // Therefore c_bar_t = -T[r, t] >= 0, d_bar_q = -T[r, m+q] >= 0, and:
    //   y_tilde_q = 1 - d_bar_q = 1 + T[r, m+q]!
    for (int q = 0; q < r; ++q) {
        for (int j = 0; j < m; ++j) at(r, j) += at(q, j);
        at(r, m + r) += at(q, m + r);
    }

    int max_pivots = 4000;
    for (int piv = 0; piv < max_pivots; ++piv) {
        // Bland's rule: first j < m+r with T[r, j] > 1e-11L
        int enter = -1;
        for (int j = 0; j < m + r; ++j) {
            if (at(r, j) > 1e-11L) {
                enter = j;
                break;
            }
        }
        if (enter == -1) {
            // Optimal!
            long double w_star = at(r, m + r);
            if (w_star > 1e-8L) {
                y_out.resize(r);
                for (int q = 0; q < r; ++q) {
                    long double dbar = -at(r, m + q);
                    long double ytilde = 1.0L - dbar;
                    y_out[q] = (long double)row_sign[q] * ytilde;
                }
                return 0; // Infeasible!
            }
            return 1; // Feasible!
        }

        // Minimum ratio test with Bland's tie-breaking (smallest basis variable index)
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
        if (leave == -1) {
            return -1; // Should never happen since w >= 0
        }

        // Pivot on (leave, enter)
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

// Finds an irreducible infeasible subset of active_eq_indices, verified by exact __int128 arithmetic.
// Returns true if infeasible (with minimal core indices in core_indices and exact weights in out_Y).
static bool gordan_minimal_core(int m, const vector<Triple>& all_eqs,
                                const vector<int>& active_eqs,
                                vector<int>& out_core_indices,
                                vector<int64_t>* out_Y = nullptr) {
    vector<long double> y;
    int status = simplex_gordan(m, all_eqs, active_eqs, y);
    if (status == 1) return false;
    if (status == -1) return false; // conservative if numeric issue

    // Keep nonzero rows sorted by increasing |y[q]| so weak rows are tested for removal first
    vector<pair<long double, int>> nonzero;
    for (size_t i = 0; i < active_eqs.size(); ++i) {
        if (fabsl(y[i]) > 1e-9L) {
            nonzero.push_back({fabsl(y[i]), active_eqs[i]});
        }
    }
    sort(nonzero.begin(), nonzero.end());
    vector<int> cur;
    cur.reserve(nonzero.size());
    for (auto& kv : nonzero) cur.push_back(kv.second);

    if (cur.empty()) cur = active_eqs;

    // Greedy minimization
    for (size_t pos = 0; pos < cur.size(); ) {
        if (cur.size() <= 2) break;
        vector<int> trial;
        trial.reserve(cur.size() - 1);
        for (size_t j = 0; j < cur.size(); ++j) {
            if (j != pos) trial.push_back(cur[j]);
        }
        vector<long double> yt;
        if (simplex_gordan(m, all_eqs, trial, yt) == 0) {
            vector<int64_t> Y_tmp;
            if (try_extract_exact_Y(m, all_eqs, trial, yt, Y_tmp)) {
                cur = std::move(trial);
                continue;
            }
        }
        ++pos;
    }

    // Exact 128-bit check on cur
    vector<long double> y_fin;
    vector<int64_t> Y_fin;
    if (simplex_gordan(m, all_eqs, cur, y_fin) == 0 &&
        try_extract_exact_Y(m, all_eqs, cur, y_fin, Y_fin)) {
        out_core_indices = std::move(cur);
        if (out_Y) *out_Y = std::move(Y_fin);
        return true;
    }
    // Fallback to raw active_eqs if shrinking lost exactness
    vector<int64_t> Y_raw;
    if (try_extract_exact_Y(m, all_eqs, active_eqs, y, Y_raw)) {
        out_core_indices.clear();
        if (out_Y) out_Y->clear();
        for (size_t i = 0; i < active_eqs.size(); ++i) {
            if (Y_raw[i] != 0) {
                out_core_indices.push_back(active_eqs[i]);
                if (out_Y) out_Y->push_back(Y_raw[i]);
            }
        }
        return !out_core_indices.empty();
    }
    return false;
}

struct CDCLSolver {
    int nvars = 0;
    vector<vector<int>> clauses;
    vector<vector<int>> watches; // watches[lit] = list of clause ids
    vector<int8_t> val;          // -1 undef, 0 false, 1 true
    vector<int8_t> phase;
    vector<int> level;
    vector<int> reason;          // clause id or -1
    vector<int> trail;
    vector<int> trail_lim;
    int qhead = 0;

    // VSIDS
    vector<double> activity;
    double var_inc = 1.0;
    vector<int> heap;
    vector<int> heap_pos;

    // Work arrays
    vector<int8_t> seen;
    vector<int> unit_queue;

    // Theory tracking: map var -> eq_idx (-1 if not an eq var)
    int m = 0;
    vector<Triple> eq_triples;
    vector<int> var_to_eq;
    vector<int> eq_to_var;
    vector<int> eq_trail;         // eq_idx currently TRUE on trail
    vector<int> eq_trail_lim;     // size of eq_trail at each decision level
    size_t last_lp_eq_size = 0;

    uint64_t conflicts = 0;
    uint64_t lp_calls = 0;
    uint64_t lp_cores = 0;
    bool record_certs = false;
    vector<pair<vector<Triple>, vector<int64_t>>> exported_certs;

    void log_cert(const vector<int>& core, const vector<int64_t>& weights) {
        if (!record_certs) return;
        vector<pair<tuple<int, int, int>, int64_t>> pairs;
        pairs.reserve(core.size());
        for (size_t i = 0; i < core.size(); ++i) {
            const Triple& tr = eq_triples[core[i]];
            pairs.push_back({{tr.i, tr.j, tr.l}, weights[i]});
        }
        sort(pairs.begin(), pairs.end(), [](const auto& a, const auto& b) { return a.first < b.first; });
        vector<Triple> ts; vector<int64_t> ys;
        ts.reserve(pairs.size()); ys.reserve(pairs.size());
        for (const auto& p : pairs) {
            ts.push_back({get<0>(p.first), get<1>(p.first), get<2>(p.first)});
            ys.push_back(p.second);
        }
        exported_certs.push_back({std::move(ts), std::move(ys)});
    }

    void init(int nv, int m_in) {
        nvars = nv;
        m = m_in;
        watches.assign(2 * nv, {});
        val.assign(nv, -1);
        phase.assign(nv, 0);
        level.assign(nv, -1);
        reason.assign(nv, -1);
        activity.assign(nv, 0.0);
        seen.assign(nv, 0);
        var_to_eq.assign(nv, -1);
        heap.resize(nv);
        heap_pos.resize(nv);
        for (int v = 0; v < nv; ++v) {
            heap[v] = v;
            heap_pos[v] = v;
        }
    }

    int declvl() const { return (int)trail_lim.size(); }
    static inline int lit_var(int l) { return l >> 1; }
    static inline int lit_sgn(int l) { return l & 1; }
    static inline int mk_lit(int v, int sgn) { return (v << 1) | sgn; }
    inline int lit_val(int l) const {
        int8_t v = val[l >> 1];
        return (v < 0) ? -1 : (v ^ (l & 1));
    }

    // Binary heap for VSIDS
    void heap_up(int i) {
        int v = heap[i];
        while (i > 0) {
            int p = (i - 1) >> 1;
            int pv = heap[p];
            if (activity[v] <= activity[pv]) break;
            heap[i] = pv; heap_pos[pv] = i;
            i = p;
        }
        heap[i] = v; heap_pos[v] = i;
    }
    void heap_down(int i) {
        int sz = (int)heap.size();
        int v = heap[i];
        while (true) {
            int c = (i << 1) + 1;
            if (c >= sz) break;
            if (c + 1 < sz && activity[heap[c + 1]] > activity[heap[c]]) c++;
            if (activity[heap[c]] <= activity[v]) break;
            heap[i] = heap[c]; heap_pos[heap[c]] = i;
            i = c;
        }
        heap[i] = v; heap_pos[v] = i;
    }
    void bump_var(int v) {
        activity[v] += var_inc;
        if (activity[v] > 1e100) {
            for (double& a : activity) a *= 1e-100;
            var_inc *= 1e-100;
        }
        if (heap_pos[v] >= 0) heap_up(heap_pos[v]);
    }
    int pop_max_heap() {
        int res = heap[0];
        int last = heap.back();
        heap.pop_back();
        heap_pos[res] = -1;
        if (!heap.empty()) {
            heap[0] = last;
            heap_pos[last] = 0;
            heap_down(0);
        }
        return res;
    }
    void insert_heap(int v) {
        if (heap_pos[v] >= 0) return;
        heap_pos[v] = (int)heap.size();
        heap.push_back(v);
        heap_up(heap_pos[v]);
    }

    bool add_base_clause(const vector<int>& lits) {
        if (lits.empty()) return false;
        if (lits.size() == 1) {
            unit_queue.push_back(lits[0]);
            return true;
        }
        int cid = (int)clauses.size();
        clauses.push_back(lits);
        watches[lits[0]].push_back(cid);
        watches[lits[1]].push_back(cid);
        return true;
    }

    bool enqueue(int p, int r) {
        int lv = lit_val(p);
        if (lv == 0) return false;
        if (lv == 1) return true;
        int v = lit_var(p);
        val[v] = (int8_t)(1 ^ lit_sgn(p));
        level[v] = declvl();
        reason[v] = r;
        phase[v] = val[v];
        trail.push_back(p);
        if (val[v] == 1 && var_to_eq[v] >= 0) {
            eq_trail.push_back(var_to_eq[v]);
        }
        return true;
    }

    void backtrack_to(int target_lvl) {
        while (declvl() > target_lvl) {
            int start = trail_lim.back();
            trail_lim.pop_back();
            for (int i = (int)trail.size() - 1; i >= start; --i) {
                int v = lit_var(trail[i]);
                val[v] = -1;
                level[v] = -1;
                reason[v] = -1;
                insert_heap(v);
            }
            trail.resize(start);
            size_t eq_sz = eq_trail_lim.back();
            eq_trail_lim.pop_back();
            eq_trail.resize(eq_sz);
        }
        qhead = (int)trail.size();
        last_lp_eq_size = eq_trail.size();
    }

    int propagate() {
        while (qhead < (int)trail.size()) {
            int p = trail[qhead++];
            int false_lit = p ^ 1;
            vector<int> ws;
            ws.swap(watches[false_lit]);
            size_t i = 0;
            for (; i < ws.size(); ++i) {
                int cid = ws[i];
                vector<int>& c = clauses[cid];
                if (c[0] == false_lit) {
                    c[0] = c[1];
                    c[1] = false_lit;
                }
                if (lit_val(c[0]) == 1) {
                    watches[false_lit].push_back(cid);
                    continue;
                }
                bool found = false;
                for (size_t k = 2; k < c.size(); ++k) {
                    if (lit_val(c[k]) != 0) {
                        c[1] = c[k];
                        c[k] = false_lit;
                        watches[c[1]].push_back(cid);
                        found = true;
                        break;
                    }
                }
                if (found) continue;
                watches[false_lit].push_back(cid);
                if (lit_val(c[0]) == 0) {
                    // Conflict!
                    for (size_t j = i + 1; j < ws.size(); ++j)
                        watches[false_lit].push_back(ws[j]);
                    return cid;
                } else {
                    enqueue(c[0], cid);
                }
            }
        }
        return -1;
    }

    void analyze(int confl_cid, vector<int>& out_learnt, int& out_btlvl) {
        out_learnt.clear();
        out_learnt.push_back(-1);
        int pathC = 0;
        int p = -1;
        int idx = (int)trail.size() - 1;
        int cur_lvl = declvl();
        do {
            const vector<int>& c = clauses[confl_cid];
            for (int q : c) {
                int v = lit_var(q);
                if (p != -1 && v == lit_var(p)) continue;
                if (!seen[v] && level[v] > 0) {
                    bump_var(v);
                    seen[v] = 1;
                    if (level[v] >= cur_lvl) {
                        pathC++;
                    } else {
                        out_learnt.push_back(q);
                    }
                }
            }
            while (!seen[lit_var(trail[idx])]) --idx;
            p = trail[idx];
            --idx;
            confl_cid = reason[lit_var(p)];
            seen[lit_var(p)] = 0;
            pathC--;
        } while (pathC > 0);

        out_learnt[0] = p ^ 1;
        for (size_t j = 1; j < out_learnt.size(); ++j) seen[lit_var(out_learnt[j])] = 0;

        if (out_learnt.size() == 1) {
            out_btlvl = 0;
        } else {
            size_t max_i = 1;
            for (size_t j = 2; j < out_learnt.size(); ++j) {
                if (level[lit_var(out_learnt[j])] > level[lit_var(out_learnt[max_i])])
                    max_i = j;
            }
            std::swap(out_learnt[1], out_learnt[max_i]);
            out_btlvl = level[lit_var(out_learnt[1])];
        }
    }

    int add_learnt_and_backjump(const vector<int>& learnt, int bt_lvl) {
        if (learnt.size() == 1) {
            backtrack_to(0);
            if (!enqueue(learnt[0], -1)) return -2; // UNSAT
        } else {
            int cid = (int)clauses.size();
            clauses.push_back(learnt);
            watches[learnt[0]].push_back(cid);
            watches[learnt[1]].push_back(cid);
            backtrack_to(bt_lvl);
            enqueue(learnt[0], cid);
        }
        return 0;
    }

    // Result: 0 = UNSAT, 1 = SAT (returns active eqs)
    int solve(vector<Triple>& sat_eqs) {
        for (int u : unit_queue) {
            if (!enqueue(u, -1)) return 0;
        }
        if (propagate() != -1) return 0;

        // Initial LP check at level 0
        if (!eq_trail.empty()) {
            vector<int> core;
            vector<int64_t> cy;
            ++lp_calls;
            if (gordan_minimal_core(m, eq_triples, eq_trail, core, record_certs ? &cy : nullptr)) {
                ++lp_cores;
                log_cert(core, cy);
                return 0;
            }
            last_lp_eq_size = eq_trail.size();
        }

        uint64_t next_restart = 100;
        uint32_t luby_u = 1, luby_v = 1;
        auto next_luby = [&]() -> uint64_t {
            uint64_t r = (uint64_t)luby_v * 100ULL;
            if ((luby_u & -luby_u) == luby_v) { luby_u++; luby_v = 1; }
            else luby_v *= 2;
            return r;
        };

        vector<int> learnt;
        while (true) {
            int confl = propagate();
            if (confl != -1) {
                ++conflicts;
                if (declvl() == 0) return 0;
                int bt_lvl = 0;
                analyze(confl, learnt, bt_lvl);
                if (add_learnt_and_backjump(learnt, bt_lvl) == -2) return 0;
                var_inc /= 0.95;
                continue;
            }

            // Eager Theory Check whenever new eqs >= 1 and total eqs >= 3
            if (eq_trail.size() >= 3 && eq_trail.size() != last_lp_eq_size) {
                last_lp_eq_size = eq_trail.size();
                ++lp_calls;
                vector<int> core;
                vector<int64_t> cy;
                if (gordan_minimal_core(m, eq_triples, eq_trail, core, record_certs ? &cy : nullptr)) {
                    ++lp_cores;
                    log_cert(core, cy);
                    ++conflicts;
                    vector<int> t_clause;
                    t_clause.reserve(core.size());
                    int max_lvl = 0;
                    for (int eq_idx : core) {
                        int v = eq_to_var[eq_idx];
                        if (level[v] > max_lvl) max_lvl = level[v];
                        t_clause.push_back(mk_lit(v, 1)); // ~eq_v
                    }
                    if (max_lvl == 0) return 0;
                    // Put max_lvl at 0 and 2nd max_lvl at 1
                    for (size_t i = 0; i < t_clause.size(); ++i) {
                        if (level[lit_var(t_clause[i])] == max_lvl) {
                            std::swap(t_clause[0], t_clause[i]);
                            break;
                        }
                    }
                    if (t_clause.size() >= 2) {
                        size_t m2 = 1;
                        for (size_t i = 2; i < t_clause.size(); ++i) {
                            if (level[lit_var(t_clause[i])] > level[lit_var(t_clause[m2])])
                                m2 = i;
                        }
                        std::swap(t_clause[1], t_clause[m2]);
                    }
                    backtrack_to(max_lvl);
                    if (t_clause.size() == 1) {
                        backtrack_to(0);
                        if (!enqueue(t_clause[0], -1)) return 0;
                        continue;
                    }
                    int t_cid = (int)clauses.size();
                    clauses.push_back(t_clause);
                    watches[t_clause[0]].push_back(t_cid);
                    watches[t_clause[1]].push_back(t_cid);
                    int bt_lvl = 0;
                    analyze(t_cid, learnt, bt_lvl);
                    if (add_learnt_and_backjump(learnt, bt_lvl) == -2) return 0;
                    var_inc /= 0.95;
                    continue;
                }
            }

            if (conflicts >= next_restart) {
                backtrack_to(0);
                next_restart = conflicts + next_luby();
                continue;
            }

            // Pick next decision variable
            int next_v = -1;
            while (!heap.empty()) {
                int cand = pop_max_heap();
                if (val[cand] == -1) {
                    next_v = cand;
                    break;
                }
            }
            if (next_v == -1) {
                // Full assignment! Verify Gordan one final time cleanly!
                vector<int> core;
                vector<int64_t> cy;
                ++lp_calls;
                if (gordan_minimal_core(m, eq_triples, eq_trail, core, record_certs ? &cy : nullptr)) {
                    ++lp_cores;
                    log_cert(core, cy);
                    if (declvl() == 0) return 0;
                    // Should have been caught above, but handle cleanly:
                    vector<int> t_clause;
                    int max_lvl = 0;
                    for (int eq_idx : core) {
                        int v = eq_to_var[eq_idx];
                        if (level[v] > max_lvl) max_lvl = level[v];
                        t_clause.push_back(mk_lit(v, 1));
                    }
                    if (max_lvl == 0) return 0;
                    for (size_t i = 0; i < t_clause.size(); ++i) {
                        if (level[lit_var(t_clause[i])] == max_lvl) {
                            std::swap(t_clause[0], t_clause[i]);
                            break;
                        }
                    }
                    if (t_clause.size() >= 2) {
                        size_t m2 = 1;
                        for (size_t i = 2; i < t_clause.size(); ++i) {
                            if (level[lit_var(t_clause[i])] > level[lit_var(t_clause[m2])]) m2 = i;
                        }
                        std::swap(t_clause[1], t_clause[m2]);
                    }
                    backtrack_to(max_lvl);
                    if (t_clause.size() == 1) {
                        backtrack_to(0);
                        if (!enqueue(t_clause[0], -1)) return 0;
                        continue;
                    }
                    int t_cid = (int)clauses.size();
                    clauses.push_back(t_clause);
                    watches[t_clause[0]].push_back(t_cid);
                    watches[t_clause[1]].push_back(t_cid);
                    int bt_lvl = 0;
                    analyze(t_cid, learnt, bt_lvl);
                    if (add_learnt_and_backjump(learnt, bt_lvl) == -2) return 0;
                    continue;
                }
                sat_eqs.clear();
                for (int eq_idx : eq_trail) sat_eqs.push_back(eq_triples[eq_idx]);
                return 1;
            }

            trail_lim.push_back((int)trail.size());
            eq_trail_lim.push_back(eq_trail.size());
            int dec_lit = mk_lit(next_v, phase[next_v] ? 0 : 1);
            enqueue(dec_lit, -1);
        }
    }
};

struct RunResult {
    int status = 0; // 0 = UNSAT, 1 = SAT
    uint64_t conflicts = 0;
    uint64_t lp_calls = 0;
    uint64_t lp_cores = 0;
    vector<Triple> sat_eqs;
    vector<pair<vector<Triple>, vector<int64_t>>> exported_certs;
};

static RunResult solve_task(const SolverTask& t, bool record_certs = false) {
    int m = t.m;
    int k = t.k;
    int ntriples = m * (m - 1) * (m - 2) / 6;

    vector<int> idx_map(m * m * m, -1);
    vector<Triple> triples;
    triples.reserve(ntriples);
    for (int i = 0; i < m; ++i) {
        for (int j = i + 1; j < m; ++j) {
            for (int l = j + 1; l < m; ++l) {
                idx_map[(i * m + j) * m + l] = (int)triples.size();
                triples.push_back({i, j, l});
            }
        }
    }
    auto tid = [&](int i, int j, int l) { return idx_map[(i * m + j) * m + l]; };

    int p3 = (t.j_elim == m - 3) ? (m - 4) : (m - 3);
    int t_low = (t.j_elim == m - 3) ? (m - 3) : (m - 2);
    int t_high = t_low + 1;

    vector<int> R;
    for (int i = 0; i < p3; ++i) {
        if (i != t.j_elim && i != t.u_low && i != t.u_high) R.push_back(i);
    }
    int nR = (int)R.size();
    int nedges = nR * (nR - 1) / 2;

    int total_vars = 3 * ntriples + nedges;
    CDCLSolver sat;
    sat.record_certs = record_certs;
    sat.init(total_vars, m);
    sat.eq_triples = triples;
    sat.eq_to_var.resize(ntriples);

    auto eq_v = [&](int idx) { return idx; };
    auto gt_v = [&](int idx) { return ntriples + idx; };
    auto lt_v = [&](int idx) { return 2 * ntriples + idx; };
    auto pos_l = [&](int v) { return CDCLSolver::mk_lit(v, 0); };
    auto neg_l = [&](int v) { return CDCLSolver::mk_lit(v, 1); };

    for (int idx = 0; idx < ntriples; ++idx) {
        int ev = eq_v(idx), gv = gt_v(idx), lv = lt_v(idx);
        sat.var_to_eq[ev] = idx;
        sat.eq_to_var[idx] = ev;
        sat.phase[ev] = 0; // prefer eq = False
        sat.phase[gv] = 0;
        sat.phase[lv] = 0;
        sat.add_base_clause({neg_l(ev), neg_l(gv)});
        sat.add_base_clause({neg_l(ev), neg_l(lv)});
        sat.add_base_clause({neg_l(gv), neg_l(lv)});
    }

    for (int idx = 0; idx < ntriples; ++idx) {
        auto [i, j, l] = triples[idx];
        int e = eq_v(idx), g = gt_v(idx), lv = lt_v(idx);
        if (l > j + 1) {
            int p = tid(i, j, l - 1);
            sat.add_base_clause({neg_l(e), pos_l(gt_v(p))});
            sat.add_base_clause({neg_l(g), pos_l(gt_v(p))});
        }
        if (l + 1 < m) {
            int p = tid(i, j, l + 1);
            sat.add_base_clause({neg_l(e), pos_l(lt_v(p))});
            sat.add_base_clause({neg_l(lv), pos_l(lt_v(p))});
        }
        if (i + 1 < j) {
            int p = tid(i + 1, j, l);
            sat.add_base_clause({neg_l(e), pos_l(gt_v(p))});
            sat.add_base_clause({neg_l(g), pos_l(gt_v(p))});
            sat.add_base_clause({neg_l(eq_v(p)), pos_l(lv)});
            sat.add_base_clause({neg_l(lt_v(p)), pos_l(lv)});
        }
        if (j + 1 < l) {
            int p = tid(i, j + 1, l);
            sat.add_base_clause({neg_l(e), pos_l(gt_v(p))});
            sat.add_base_clause({neg_l(g), pos_l(gt_v(p))});
            sat.add_base_clause({neg_l(eq_v(p)), pos_l(lv)});
            sat.add_base_clause({neg_l(lt_v(p)), pos_l(lv)});
        }
        if (i + 1 == j && j + 1 < l) {
            int p = tid(i + 1, j + 1, l);
            sat.add_base_clause({neg_l(e), pos_l(gt_v(p))});
            sat.add_base_clause({neg_l(g), pos_l(gt_v(p))});
            sat.add_base_clause({neg_l(eq_v(p)), pos_l(lv)});
            sat.add_base_clause({neg_l(lt_v(p)), pos_l(lv)});
        }
    }

    for (int l = 2; l < m; ++l) {
        for (int x = 0; x < l; ++x) {
            vector<int> cands;
            for (int y = 0; y < l; ++y) {
                if (y != x) cands.push_back(eq_v(tid(min(x, y), max(x, y), l)));
            }
            for (size_t p = 0; p < cands.size(); ++p) {
                for (size_t q = p + 1; q < cands.size(); ++q) {
                    sat.add_base_clause({neg_l(cands[p]), neg_l(cands[q])});
                }
            }
        }
    }

    // Step 2: x_{m-2} + x_j = x_{m-1}
    if (t.j_elim < 0) {
        for (int i = 0; i < m - 2; ++i) {
            sat.add_base_clause({neg_l(eq_v(tid(i, m - 2, m - 1)))});
        }
    } else {
        sat.add_base_clause({pos_l(eq_v(tid(t.j_elim, m - 2, m - 1)))});
    }

    // Step 3: u_low and u_high
    if (t.u_low < 0) {
        for (int i = 0; i < p3; ++i) {
            if (i != t.j_elim) sat.add_base_clause({neg_l(eq_v(tid(i, p3, t_low)))});
        }
    } else {
        sat.add_base_clause({pos_l(eq_v(tid(t.u_low, p3, t_low)))});
    }

    if (t.u_high < 0) {
        for (int i = 0; i < p3; ++i) {
            if (i != t.j_elim) sat.add_base_clause({neg_l(eq_v(tid(i, p3, t_high)))});
        }
    } else {
        sat.add_base_clause({pos_l(eq_v(tid(t.u_high, p3, t_high)))});
    }

    // Edges in R
    vector<int> edge_var(nR * nR, -1);
    int cur_ev = 3 * ntriples;
    for (int ai = 0; ai < nR; ++ai) {
        for (int bi = ai + 1; bi < nR; ++bi) {
            int ev = cur_ev++;
            edge_var[ai * nR + bi] = ev;
            sat.phase[ev] = 1; // edges needed to avoid clique-free subgraphs
            vector<int> cl = {neg_l(ev)};
            int a = R[ai], b = R[bi];
            for (int l = b + 1; l < m; ++l) {
                cl.push_back(pos_l(eq_v(tid(a, b, l))));
            }
            sat.add_base_clause(cl);
        }
    }

    // Give higher VSIDS initial activity to edge variables so graph structure drives search
    for (int v = 3 * ntriples; v < total_vars; ++v) {
        sat.activity[v] = 10.0;
        sat.heap_up(sat.heap_pos[v]);
    }

    // Enumerate all (k - 2)-subsets of R
    int sub_sz = k - 2;
    vector<int> comb(sub_sz);
    auto emit_combs = [&](auto& self, int idx_start, int depth) -> void {
        if (depth == sub_sz) {
            vector<int> cl;
            cl.reserve(sub_sz * (sub_sz - 1) / 2);
            for (int p = 0; p < sub_sz; ++p) {
                for (int q = p + 1; q < sub_sz; ++q) {
                    cl.push_back(pos_l(edge_var[comb[p] * nR + comb[q]]));
                }
            }
            sat.add_base_clause(cl);
            return;
        }
        for (int i = idx_start; i <= nR - (sub_sz - depth); ++i) {
            comb[depth] = i;
            self(self, i + 1, depth + 1);
        }
    };
    emit_combs(emit_combs, 0, 0);

    RunResult res;
    res.status = sat.solve(res.sat_eqs);
    res.conflicts = sat.conflicts;
    res.lp_calls = sat.lp_calls;
    res.lp_cores = sat.lp_cores;
    if (record_certs) res.exported_certs = std::move(sat.exported_certs);
    return res;
}

static vector<SolverTask> build_tasks(int m, int k, const vector<int>& j_list) {
    vector<SolverTask> tasks;
    for (int j_elim : j_list) {
        int p3 = (j_elim == m - 3) ? (m - 4) : (m - 3);
        vector<int> avail = {-1};
        for (int i = 0; i < p3; ++i) {
            if (i != j_elim) avail.push_back(i);
        }
        for (int u_low : avail) {
            for (int u_high : avail) {
                if (u_low >= 0 && u_high >= 0 && u_low >= u_high) continue;
                tasks.push_back({m, k, j_elim, u_low, u_high});
            }
        }
    }
    return tasks;
}

static bool run_suite(int m, int k, const vector<int>& j_list, const string& export_path = "") {
    auto tasks = build_tasks(m, k, j_list);
    int N = (int)tasks.size();
    bool do_export = !export_path.empty();
    cout << "m=" << m << ", k=" << k << " [C++ CDCL(T)]: Running " << N
         << " tasks across " << omp_get_max_threads() << " threads..." << endl;
    auto t0 = chrono::steady_clock::now();

    uint64_t tot_conf = 0, tot_lp = 0, tot_cores = 0;
    int done = 0;
    bool any_sat = false;
    SolverTask sat_task;
    vector<Triple> sat_eqs;
    vector<pair<vector<Triple>, vector<int64_t>>> all_certs;

    #pragma omp parallel for schedule(dynamic, 1)
    for (int idx = 0; idx < N; ++idx) {
        bool abort_flag;
        #pragma omp atomic read
        abort_flag = any_sat;
        if (abort_flag) continue;

        RunResult r = solve_task(tasks[idx], do_export);

        #pragma omp critical
        {
            done++;
            tot_conf += r.conflicts;
            tot_lp += r.lp_calls;
            tot_cores += r.lp_cores;
            if (do_export) {
                for (auto& c : r.exported_certs) all_certs.push_back(std::move(c));
            }
            if (r.status == 1 && !any_sat) {
                any_sat = true;
                sat_task = tasks[idx];
                sat_eqs = r.sat_eqs;
            }
            if (done % 50 == 0 || done == N) {
                double wall = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
                cout << "  progress: " << done << "/" << N
                     << " | conf=" << tot_conf
                     << " | lp_calls=" << tot_lp
                     << " | cores=" << tot_cores
                     << " | wall=" << fixed << setprecision(2) << wall << "s" << endl;
            }
        }
    }

    double wall = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (any_sat) {
        cout << "*** CANDIDATE SAT FOUND at task=(" << sat_task.j_elim << "," << sat_task.u_low
             << "," << sat_task.u_high << ") with " << sat_eqs.size() << " eqs:" << endl;
        for (auto& tr : sat_eqs) cout << "(" << tr.i << "," << tr.j << "," << tr.l << ") ";
        cout << endl;
        return false;
    }

    size_t unique_count = 0, max_terms = 0, gt8_terms = 0;
    if (do_export) {
        auto triple_lt = [](const Triple& a, const Triple& b) {
            return tie(a.i, a.j, a.l) < tie(b.i, b.j, b.l);
        };
        auto vec_lt = [&](const pair<vector<Triple>, vector<int64_t>>& a,
                          const pair<vector<Triple>, vector<int64_t>>& b) {
            if (a.first.size() != b.first.size()) return a.first.size() < b.first.size();
            return lexicographical_compare(a.first.begin(), a.first.end(),
                                           b.first.begin(), b.first.end(), triple_lt);
        };
        sort(all_certs.begin(), all_certs.end(), vec_lt);
        ofstream fout(export_path, ios::app);
        if (!fout) {
            cerr << "ERROR: Failed to open export file: " << export_path << endl;
            return false;
        }
        const vector<Triple>* prev = nullptr;
        for (const auto& kv : all_certs) {
            if (prev && kv.first.size() == prev->size() &&
                equal(kv.first.begin(), kv.first.end(), prev->begin(),
                      [](const Triple& a, const Triple& b) { return a.i == b.i && a.j == b.j && a.l == b.l; })) {
                continue;
            }
            prev = &kv.first;
            unique_count++;
            if (kv.first.size() > max_terms) max_terms = kv.first.size();
            if (kv.first.size() > 8) gt8_terms++;
            fout << "{\"m\":" << m << ",\"k\":" << k << ",\"triples\":[";
            for (size_t q = 0; q < kv.first.size(); ++q) {
                if (q) fout << ",";
                fout << "[" << kv.first[q].i << "," << kv.first[q].j << "," << kv.first[q].l << "]";
            }
            fout << "],\"weights\":[";
            for (size_t q = 0; q < kv.second.size(); ++q) {
                if (q) fout << ",";
                fout << kv.second[q];
            }
            fout << "]}\n";
        }
    }

    cout << "ALL " << N << " TASKS FOR m=" << m << ", k=" << k
         << " PROVEN UNSAT (100% __int128 verified) in " << fixed << setprecision(2)
         << wall << "s (tot_cores=" << tot_cores << ", lp_calls=" << tot_lp;
    if (do_export) {
        cout << ", unique_exported=" << unique_count << ", max_terms=" << max_terms << ", gt8_terms=" << gt8_terms;
    }
    cout << ")!" << endl;
    return true;
}

int main(int argc, char** argv) {
    string cmd = "selftest";
    string export_path = "";
    for (int i = 1; i < argc; ++i) {
        string a = argv[i];
        if (a == "--export-certs" && i + 1 < argc) {
            export_path = argv[++i];
        } else {
            cmd = a;
        }
    }
    if (!export_path.empty()) {
        ofstream clear_out(export_path, ios::trunc);
    }
    if (cmd == "selftest") {
        vector<int> j4 = {-1};
        for (int i = 0; i < 9; ++i) j4.push_back(i);
        if (!run_suite(11, 4, j4, export_path)) return 1;
        vector<int> j5 = {-1};
        for (int i = 0; i < 14; ++i) j5.push_back(i);
        if (!run_suite(16, 5, j5, export_path)) return 1;
    } else if (cmd == "caseA") {
        if (!run_suite(22, 6, {-1}, export_path)) return 1;
    } else if (cmd == "caseB") {
        vector<int> j6;
        for (int i = 0; i < 20; ++i) j6.push_back(i);
        if (!run_suite(22, 6, j6, export_path)) return 1;
    } else if (cmd == "all") {
        vector<int> j6 = {-1};
        for (int i = 0; i < 20; ++i) j6.push_back(i);
        if (!run_suite(22, 6, j6, export_path)) return 1;
    } else {
        vector<int> j6;
        stringstream ss(cmd);
        string tok;
        while (getline(ss, tok, ',')) {
            if (tok == "None" || tok == "-1") j6.push_back(-1);
            else j6.push_back(stoi(tok));
        }
        if (!run_suite(22, 6, j6, export_path)) return 1;
    }
    return 0;
}
