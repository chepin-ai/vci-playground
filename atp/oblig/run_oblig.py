#!/usr/bin/env python3
"""ATP-LAB obligation-machine suite runner.

Runs P1 (Prover9/Mace4 lattice proof + dual controls), P2 (Z3 BMC),
P3 (cvc5 Galois connection) and appends one JSONL record per conclusion:
  {ts, suite, engine, property, role, verdict, witness}
`witness` is a truncated proof/countermodel/trace summary (no secrets).

Usage: run_oblig.py <output.jsonl>
Exit 0 iff every verdict matches its expected polarity (dual discipline:
each "proved" is paired with a "refutation failed" control).
"""
import datetime
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SUITE = "atp-oblig"
MAX_WITNESS = 600

records = []
failures = []


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run(cmd, timeout=300, env=None):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout,
                       cwd=HERE, env=env)
    return p.returncode, p.stdout + p.stderr


def trunc(s, n=MAX_WITNESS):
    s = re.sub(r"\s+", " ", s).strip()
    return s if len(s) <= n else s[: n - 3] + "..."


def record(engine, prop, role, verdict, witness, expect_ok):
    records.append({
        "ts": now(), "suite": SUITE, "engine": engine, "property": prop,
        "role": role, "verdict": verdict, "witness": trunc(witness),
    })
    if not expect_ok:
        failures.append(f"{engine}:{prop}:{role} -> {verdict}")


def need(tool):
    path = shutil.which(tool)
    if not path:
        record(tool, "setup", "setup", "missing", f"{tool} not on PATH", False)
    return path


def main():
    out_jsonl = sys.argv[1]
    prover9, mace4 = need("prover9"), need("mace4")

    # ---------------- P1: 7-state obligation lattice ----------------
    if prover9:
        rc, out = run([prover9, "-f", "p1_lattice_pos.in"])
        ok = "THEOREM PROVED" in out
        m = re.search(r"proofs\s+(\d+).*?kept\s+(\d+)", out, re.S)
        record("prover9", "P1_obligation_poset_is_lattice", "positive",
               "proved" if ok else "not_proved",
               f"goal: join/meet are lub/glb over 7-state obligation poset; "
               f"Prover9 THEOREM PROVED={ok}", ok)

    if mace4:
        # control: no countermodel to the lattice claim may exist (size 7)
        rc, out = run([mace4, "-f", "p1_lattice_control.in"])
        n_models = out.count("interpretation(")
        exhausted = "exit (exhausted)" in out
        ok = n_models == 0 and exhausted
        record("mace4", "P1_obligation_poset_is_lattice", "control",
               "refutation_failed" if ok else "countermodel_found",
               f"size-7 countermodel search to lattice claim: models={n_models}, "
               f"exhausted={exhausted} (expected 0/exhausted)", ok)

        # refutation: the wrong claim "every lattice is a total order"
        rc, out = run([mace4, "-f", "p1_not_total.in"])
        n_models = out.count("interpretation(")
        ok = n_models > 0
        interp = ""
        m = re.search(r"(interpretation\(.*?\]\)\.\n)", out, re.S)
        if m:
            interp = m.group(1)
        record("mace4", "P1_every_lattice_is_total_order", "refutation",
               "countermodel_found" if ok else "no_countermodel",
               "finite non-total lattice (incomparable c1,c2): " + interp, ok)

    # ---------------- P2: Z3 bounded model checking ----------------
    if shutil.which("python3"):
        rc, out = run([sys.executable or "python3", "p2_bmc.py"])
        va = re.search(r"P2A_VERDICT=(\w+)", out)
        vb = re.search(r"P2B_VERDICT=(\w+)", out)
        da = re.search(r"P2A_DETAIL=(.*)", out)
        tb = re.search(r"P2B_TRACE=(.*)", out)
        record("z3", "P2_dual_queue_nonblocking_k8", "positive",
               va.group(1) if va else "error",
               da.group(1) if da else trunc(out),
               bool(va and va.group(1) == "unsat"))
        record("z3", "P2_single_fifo_starvation_k8", "refutation",
               vb.group(1) if vb else "error",
               "counter-trace: " + (tb.group(1) if tb else trunc(out)),
               bool(vb and vb.group(1) == "sat"))

    # ---------------- P3: cvc5 Galois connection ----------------
    if shutil.which("python3"):
        rc, out = run([sys.executable or "python3", "p3_run.py"])
        va = re.search(r"P3A_VERDICT=(\w+)", out)
        vb = re.search(r"P3B_VERDICT=(\w+)", out)
        da = re.search(r"P3A_DETAIL=(.*)", out)
        wb = re.search(r"P3B_WITNESS=(.*)", out)
        record("cvc5", "P3_galois_connection_4x4_valid", "positive",
               va.group(1) if va else "error",
               da.group(1) if da else trunc(out),
               bool(va and va.group(1) == "unsat"))
        record("cvc5", "P3_galois_connection_4x4_broken", "control",
               vb.group(1) if vb else "error",
               "violating-pair witness (o,e): " + (wb.group(1) if wb else trunc(out)),
               bool(vb and vb.group(1) == "sat"))

    os.makedirs(os.path.dirname(out_jsonl), exist_ok=True)
    with open(out_jsonl, "a") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    print(json.dumps(records, indent=2, ensure_ascii=False))
    if failures:
        print("UNEXPECTED VERDICTS: " + "; ".join(failures), file=sys.stderr)
        sys.exit(1)
    print("ALL_VERDICTS_AS_EXPECTED")


if __name__ == "__main__":
    main()
