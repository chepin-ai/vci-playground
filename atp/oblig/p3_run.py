#!/usr/bin/env python3
"""P3 driver: run cvc5 over the two Galois-connection smt2 files.

Prints stable harvest lines:
  P3A_VERDICT=unsat|sat|unknown   (p3_galois_valid.smt2, expect unsat)
  P3B_VERDICT=unsat|sat|unknown   (p3_galois_broken.smt2, expect sat)
  P3B_WITNESS=(o e) values        (counterexample witness)
  P3_VERSION=<cvc5 version>
Exit 0 iff both verdicts match expectations.
"""
import importlib.metadata
import os
import sys

import cvc5

HERE = os.path.dirname(os.path.abspath(__file__))


def run_smt2(path):
    solver = cvc5.Solver()
    sm = cvc5.SymbolManager(solver)
    parser = cvc5.InputParser(solver, sm)
    with open(path) as f:
        text = f.read()
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, text, os.path.basename(path))
    outputs = []
    while True:
        cmd = parser.nextCommand()
        if cmd.isNull():
            break
        r = cmd.invoke(solver, sm)
        if r is not None and str(r).strip():
            outputs.append(str(r).strip())
    return outputs


def main():
    ok = True
    out_a = run_smt2(os.path.join(HERE, "p3_galois_valid.smt2"))
    verdict_a = out_a[0] if out_a else "unknown"
    print(f"P3A_VERDICT={verdict_a}")
    if verdict_a != "unsat":
        print("P3A_UNEXPECTED: expected unsat (valid Galois connection)")
        ok = False
    else:
        print("P3A_DETAIL=alpha(o)=o div 2, gamma(e)=min(3,2e+1): no violating "
              "(o,e) pair in 4x4; Galois axiom holds (unsat)")

    out_b = run_smt2(os.path.join(HERE, "p3_galois_broken.smt2"))
    verdict_b = out_b[0] if out_b else "unknown"
    print(f"P3B_VERDICT={verdict_b}")
    if verdict_b != "sat":
        print("P3B_UNEXPECTED: expected sat (broken adjoint must have a witness)")
        ok = False
    else:
        witness = out_b[1] if len(out_b) > 1 else "?"
        print(f"P3B_WITNESS={witness}")

    print(f"P3_VERSION={importlib.metadata.version('cvc5')}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
