#!/usr/bin/env python3
"""P6: Whittle-index admission invariants under tick updates (Z3).

Toy restless-bandit scheduling layer: n=4 arms, arm i has Whittle index
w[i] and resource cost c[i]; activating arm i consumes w[i]*c[i] of the
budget. Each tick a scheduler proposes an active set P; the admission
controller accepts P iff
    budget:   sum_{i in P} w[i]*c[i] <= B
    capacity: |P| <= K_MAX
otherwise the previous active set persists (rejection is not a violation).

Instance: w*c = [1, 2, 1, 3], B = 4, K_MAX = 2 (both constraints binding:
{1,3} breaks the budget, any 3-set breaks the capacity).

P6a (positive, BMC k=6):
    Starting from any invariant-satisfying set, the invariant holds at all
    ticks 0..6 under the guarded update. Check: negation -> UNSAT.

P6b (positive, inductive step):
    inv(t) and one guarded update imply inv(t+1), with the state at t
    fully symbolic. Check: negation -> UNSAT.

P6c (refutation, capacity check removed):
    With budget-only admission, a 3-arm proposal {0,1,2}
    (w*c sum = 1+2+1 = 4 <= B) is accepted and violates |A| <= K_MAX.
    Check: SAT with a concrete counter-trace.

Exit 0 iff all three verdicts match expectations; witness lines are printed
with a stable prefix for the runner to harvest.
"""
import sys

import z3

K = 6                      # BMC bound
N_ARMS = 4
WC = [1, 2, 1, 3]          # per-arm Whittle-index * cost
B = 4                      # budget
K_MAX = 2                  # capacity


def budget_expr(a):
    return z3.Sum([z3.If(a[i], WC[i], 0) for i in range(N_ARMS)])


def size_expr(a):
    return z3.Sum([z3.If(a[i], 1, 0) for i in range(N_ARMS)])


def inv(a):
    return z3.And(budget_expr(a) <= B, size_expr(a) <= K_MAX)


def arms(t, tag):
    return z3.Bools(" ".join(f"{tag}{i}_t{t}" for i in range(N_ARMS)))


def guarded_update(sol, a_prev, a_next, use_capacity):
    """One tick: an arbitrary proposal is admitted iff it passes the checks
    that are enabled; on rejection the previous set persists."""
    p = z3.Bools(" ".join(f"prop{i}" for i in range(N_ARMS)))
    checks = [budget_expr(p) <= B]
    if use_capacity:
        checks.append(size_expr(p) <= K_MAX)
    admitted = z3.And(checks)
    for i in range(N_ARMS):
        sol.add(a_next[i] == z3.If(admitted, p[i], a_prev[i]))
    return p, admitted


def p6a_bmc():
    sol = z3.Solver()
    states = [arms(t, "a") for t in range(K + 1)]
    sol.add(inv(states[0]))
    for t in range(K):
        guarded_update(sol, states[t], states[t + 1], use_capacity=True)
    # negated bounded safety: some tick violates the invariant
    sol.add(z3.Not(z3.And([inv(states[t]) for t in range(K + 1)])))
    res = sol.check()
    print(f"P6A_VERDICT={res}")
    if res != z3.unsat:
        print("P6A_UNEXPECTED: expected unsat (invariant must hold for k=6)")
        if res == z3.sat:
            print(sol.model())
        return False
    print("P6A_DETAIL=budget sum(w_i*c_i)<=4 and |A|<=2 hold at all ticks "
          "0..6 under guarded admission; negation UNSAT")
    return True


def p6b_inductive_step():
    sol = z3.Solver()
    a_t = arms(0, "s")
    a_t1 = arms(1, "s")
    sol.add(inv(a_t))                       # invariant at t (symbolic state)
    guarded_update(sol, a_t, a_t1, use_capacity=True)
    sol.add(z3.Not(inv(a_t1)))              # but violated at t+1
    res = sol.check()
    print(f"P6B_VERDICT={res}")
    if res != z3.unsat:
        print("P6B_UNEXPECTED: expected unsat (induction step must hold)")
        if res == z3.sat:
            print(sol.model())
        return False
    print("P6B_DETAIL=inv(t) & guarded-update ==> inv(t+1) for symbolic "
          "state; one-step induction UNSAT")
    return True


def p6c_no_capacity_check():
    sol = z3.Solver()
    states = [arms(t, "c") for t in range(K + 1)]
    sol.add(inv(states[0]))
    for t in range(K):
        guarded_update(sol, states[t], states[t + 1], use_capacity=False)
    # capacity violated somewhere while the budget still holds everywhere
    sol.add(z3.Or([size_expr(states[t]) > K_MAX for t in range(K + 1)]))
    sol.add(z3.And([budget_expr(states[t]) <= B for t in range(K + 1)]))
    res = sol.check()
    print(f"P6C_VERDICT={res}")
    if res != z3.sat:
        print("P6C_UNEXPECTED: expected sat (capacity-violation trace)")
        return False
    m = sol.model()
    trace = ", ".join(
        "t{}:(A={{{}}},sum={},|A|={})".format(
            t,
            ",".join(str(i) for i in range(N_ARMS) if z3.is_true(m.eval(states[t][i]))),
            m.eval(budget_expr(states[t])),
            m.eval(size_expr(states[t])))
        for t in range(K + 1))
    print(f"P6C_TRACE={trace}")
    return True


if __name__ == "__main__":
    ok = all([p6a_bmc(), p6b_inductive_step(), p6c_no_capacity_check()])
    print(f"P6_VERSION={z3.get_version_string()}")
    sys.exit(0 if ok else 1)
