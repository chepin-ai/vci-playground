#!/usr/bin/env python3
"""P2: bounded model checking (Z3) of obligation-machine queueing properties.

P2a (positive, dual-queue non-blocking):
    One shared server alternates fairly between the machine FIFO queue and the
    human-domain ladder. A machine obligation is enqueued at t=0. A human
    obligation with (approximately) infinite clearing time sits on the ladder.
    Property: within k=8 steps the machine obligation is still processed
    (bounded liveness). Check: negation is UNSAT.

P2b (counterexample variant, single strict FIFO):
    One strict FIFO queue, head-of-line blocking: the human obligation (same
    near-infinite clearing time) sits at the head, the machine obligation
    behind it. The machine obligation can starve. Check: negation (never
    processed within k=8) is SAT and yields a concrete counter-trace.

Exit code 0 iff both verdicts match expectations; witness lines are printed
with a stable prefix for the runner to harvest.
"""
import sys
import z3

K = 8          # bound
INF = 1000     # near-infinite clearing time for human-domain obligations


def p2a_dual_queue():
    s = z3.Solver()
    done = z3.Bools(" ".join(f"done_{t}" for t in range(K + 1)))
    proc = z3.Bools(" ".join(f"proc_{t}" for t in range(K)))
    hrem = z3.Ints(" ".join(f"hrem_{t}" for t in range(K + 1)))

    # machine obligation enqueued at t=0, not yet processed
    s.add(done[0] == False)
    # human obligation on the ladder with near-infinite clearing time
    s.add(hrem[0] == INF)
    for t in range(K):
        serve_machine = (t % 2 == 0)  # fair alternation: even slots -> machine queue
        # machine obligation processed exactly on a machine slot while pending
        s.add(proc[t] == z3.And(serve_machine, z3.Not(done[t])))
        s.add(done[t + 1] == z3.Or(done[t], proc[t]))
        # human ladder advances only on its own slots; never reaches 0 in-window
        if t % 2 == 1:
            s.add(hrem[t + 1] == z3.If(hrem[t] > 0, hrem[t] - 1, 0))
        else:
            s.add(hrem[t + 1] == hrem[t])
        # dual-track discipline: human backpressure never steals machine slots
        # (structural: serve_machine depends only on t, not on hrem)

    # negated bounded liveness: machine obligation never processed within k steps
    s.add(z3.Not(done[K]))
    r = s.check()
    print(f"P2A_VERDICT={r}")
    if r != z3.unsat:
        print("P2A_UNEXPECTED: expected unsat (machine obligation must be served)")
        if r == z3.sat:
            print(s.model())
        return False
    print("P2A_DETAIL=dual-queue fair alternation: machine obligation processed "
          "despite human clearing time=1000 >> k=8; negation UNSAT")
    return True


def p2b_single_fifo_starvation():
    s = z3.Solver()
    hrem = z3.Ints(" ".join(f"hrem_{t}" for t in range(K + 1)))
    done = z3.Bools(" ".join(f"done_{t}" for t in range(K + 1)))

    # strict FIFO: human obligation at head (clearing time ~inf), machine behind
    s.add(hrem[0] == INF)
    s.add(done[0] == False)
    for t in range(K):
        # head advances only when its clearing time elapses
        s.add(hrem[t + 1] == z3.If(hrem[t] > 0, hrem[t] - 1, 0))
        # machine obligation served only once the head has cleared
        s.add(done[t + 1] == z3.Or(done[t], hrem[t] == 0))

    # starvation claim: machine obligation never processed within k steps
    s.add(z3.Not(done[K]))
    r = s.check()
    print(f"P2B_VERDICT={r}")
    if r != z3.sat:
        print("P2B_UNEXPECTED: expected sat (starvation counter-trace)")
        return False
    m = s.model()
    trace = ", ".join(
        f"t{t}:(hrem={m.eval(hrem[t])},done={m.eval(done[t])})" for t in range(K + 1))
    print(f"P2B_TRACE={trace}")
    return True


if __name__ == "__main__":
    ok_a = p2a_dual_queue()
    ok_b = p2b_single_fifo_starvation()
    print(f"P2_VERSION={z3.get_version_string()}")
    sys.exit(0 if (ok_a and ok_b) else 1)
