#!/usr/bin/env python3
"""CHGS-01 wave-1: combinatorial-complex (CC) unified skeleton + spectral/SVD residual smoke.

Unifies the vci-usrm knowledge graph (roadmap) and obligation ledger into one
Combinatorial Complex (Hajij et al., arXiv:2206.00606 -- CCs subsume graphs,
hypergraphs and (simplicial/cell) complexes via a rank function on cells), then
runs two computations on it and applies a residual ("落链") verdict.

Inputs (fetched by the caller; this script never touches the network):
  --roadmap      ure/roadmap.json      (12 nodes, deps edges, findings capsules)
  --obligations  ure/obligations.jsonl (obligation ledger; '#' comment lines)

CC construction
  rank-0: roadmap node ids + obligation ids + evidence items (NOTE-DEV-1)
  rank-1: deps edges (node -> dep) + obligation<->evidence pairs
  rank-2: capsule hyperedges -- a roadmap finding whose note references >=2 other
          roadmap nodes becomes one rank-2 cell over {host} U referenced nodes
          (hypergraph-style higher cell; CCs natively host such cells).

S1  CC stats: per-rank cell counts, incidence matrix shapes (B1: rank0 x rank1,
    B2: rank1 x rank2), connected components of the rank-1 skeleton.
S2a spectral: signed node-edge incidence B1, combinatorial (Hodge) Laplacian
    L0 = B1 B1^T (Schaub et al. convention), spectrum via numpy eigvalsh;
    first 5 eigenvalues reported; lambda2 ~ 0 signals broken connectivity.
S2b tensorization: truncated SVD of L0 at rank k=3 (for symmetric PSD L0 the
    SVD coincides with the truncated eigendecomposition of the spectral vector
    field); relative Frobenius error eps = ||L0 - L0_k||_F / ||L0||_F.
S3  verdict: eps > 0.15 OR lambda2 ~ 0  -> record {"type": "chgs_residual", ...}
    else -> {"type": "chgs_clean", ...}.  Same JSONL pipeline shape as tn/results.

NOTE-DEV-1 (deviation from brief, documented): the brief pins rank-0 to
nodes/obligations only. Evidence items are added as rank-0 cells so that each
obligation<->evidence pair is a rank-1 cell with a proper 2-point boundary;
otherwise obligations would be isolated 0-cells with no incident 1-cells.

NOTE-LIB (library tradeoff): toponetx 0.4.0 pip-installs cleanly on py3.12, so
it is used as the CC container/validator (rank structure, cell membership).
The signed incidence B1 is assembled directly with numpy because toponetx 0.4
exposes unsigned incidence only, and L0 = B1 B1^T needs an (arbitrary but
consistent) orientation. networkx is used for connected-component analysis of
the rank-1 skeleton. Fallback if toponetx ever breaks in CI: the self-built
rank dicts below are already the source of truth; the toponetx container is a
mirror, so swapping it out is a ~10-line change.

Security: output contains only counts, numeric values and node ids -- no secrets,
no identifiers beyond public roadmap/obligation ids.
"""

import argparse
import json
import re
import sys
from collections import defaultdict

import numpy as np

EPS_THRESHOLD = 0.15
SVD_RANK = 3
GAP_TOL = 1e-8  # integer Laplacian: numerical zeros are ~1e-15

NODE_RE = re.compile(r"n(?:10|[1-9]a?)(?![0-9a-z])")  # n1..n9, n1a, n10


def load_roadmap(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def load_obligations(path):
    out = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                out.append(json.loads(line))
    return out


def build_cc(roadmap, obligations):
    """Return rank structures + toponetx mirror container."""
    nodes = roadmap["nodes"]
    node_ids = [n["id"] for n in nodes]
    node_set = set(node_ids)

    rank0 = list(node_ids)
    rank1 = []  # (cell_id, endpoint_a, endpoint_b, kind)
    rank2 = []  # (cell_id, frozenset(node ids))

    # --- rank-1: deps edges (oriented node -> dep) ---
    for n in nodes:
        for dep in n.get("deps", []):
            if dep in node_set:
                rank1.append((f"dep:{n['id']}->{dep}", n["id"], dep, "dep"))

    # --- obligations: rank-0 obligation cells + rank-1 obligation<->evidence ---
    for ob in obligations:
        oid = ob["id"]
        rank0.append(oid)
        for i, _ev in enumerate(ob.get("evidence", [])):
            ev_id = f"{oid}#ev{i}"  # evidence text itself is never emitted
            rank0.append(ev_id)
            rank1.append((f"obev:{oid}#{i}", oid, ev_id, "obligation_evidence"))

    # --- rank-2: capsule hyperedges from findings referencing >=2 other nodes ---
    for n in nodes:
        host = n["id"]
        for f_ in n.get("findings", []):
            refs = {r for r in NODE_RE.findall(f_.get("note", "").lower())
                    if r in node_set and r != host}
            if len(refs) >= 2:
                members = frozenset({host} | refs)
                rank2.append((f"cap:{f_.get('hash', host)}", members))

    # --- toponetx mirror container (validation of CC semantics) ---
    tnx_status = "skipped"
    try:
        from toponetx.classes import CombinatorialComplex
        cc = CombinatorialComplex()
        for c in rank0:
            cc.add_cell((c,), rank=0)
        for cid, a, b, _k in rank1:
            cc.add_cell((a, b), rank=1)
        for cid, members in rank2:
            cc.add_cell(tuple(sorted(members)), rank=2)
        # sanity: every rank-1 cell is present, ranks respected
        assert all((a, b) in cc or (b, a) in cc for _c, a, b, _k in rank1)
        assert all(tuple(sorted(m)) in cc for _c, m in rank2)
        tnx_status = "ok"
    except ImportError:
        # Fallback path: self-built rank dicts above remain the source of truth.
        tnx_status = "toponetx-unavailable(self-built-ranks)"
        cc = None

    return {
        "rank0": rank0,
        "rank1": rank1,
        "rank2": rank2,
        "tnx": tnx_status,
        "cc": cc,
    }


def incidence_b1(rank0, rank1):
    """Signed node-edge incidence (orientation = listed order)."""
    idx = {c: i for i, c in enumerate(rank0)}
    B1 = np.zeros((len(rank0), len(rank1)), dtype=float)
    for j, (_cid, a, b, _k) in enumerate(rank1):
        B1[idx[a], j] = -1.0
        B1[idx[b], j] = +1.0
    return B1


def incidence_b2(rank1, rank2):
    """Edge-in-hyperedge incidence (unsigned membership; deps edges fully
    contained in the rank-2 member set)."""
    edge_nodes = [frozenset((a, b)) for _c, a, b, _k in rank1]
    B2 = np.zeros((len(rank1), len(rank2)), dtype=float)
    for j, (_cid, members) in enumerate(rank2):
        for i, en in enumerate(edge_nodes):
            if en <= members:
                B2[i, j] = 1.0
    return B2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--roadmap", required=True)
    ap.add_argument("--obligations", required=True)
    ap.add_argument("--out-jsonl", required=True, help="append one JSONL record here")
    ap.add_argument("--out-summary", required=True, help="pretty JSON summary here")
    ap.add_argument("--ts", required=True)
    args = ap.parse_args()

    import importlib.metadata
    import networkx as nx

    roadmap = load_roadmap(args.roadmap)
    obligations = load_obligations(args.obligations)
    built = build_cc(roadmap, obligations)
    rank0, rank1, rank2 = built["rank0"], built["rank1"], built["rank2"]

    # ---------- S1: CC stats ----------
    B1 = incidence_b1(rank0, rank1)
    B2 = incidence_b2(rank1, rank2)
    G = nx.Graph()
    G.add_nodes_from(range(len(rank0)))
    idx = {c: i for i, c in enumerate(rank0)}
    for _cid, a, b, _k in rank1:
        G.add_edge(idx[a], idx[b])
    n_components = nx.number_connected_components(G)
    cc_stats = {
        "rank0": len(rank0),
        "rank1": len(rank1),
        "rank2": len(rank2),
        "rank1_by_kind": {str(k_): int(v_) for k_, v_ in
                          zip(*np.unique([k for *_x, k in rank1], return_counts=True))} if rank1 else {},
        "B1_shape": list(B1.shape),
        "B2_shape": list(B2.shape),
        "B2_nnz": int(np.count_nonzero(B2)),
        "components": int(n_components),
        "rank2_cells": [sorted(m) for _c, m in rank2],
        "cc_container": built["tnx"],
    }
    print("S1 cc_stats:", json.dumps(cc_stats, ensure_ascii=False))

    # ---------- S2a: combinatorial Laplacian spectrum ----------
    L0 = B1 @ B1.T
    eigs = np.linalg.eigvalsh(L0)  # ascending; |x|<GAP_TOL is numerical zero
    eigs = np.where(np.abs(eigs) < GAP_TOL, 0.0, eigs)
    first5 = [round(float(x), 10) for x in eigs[:5]]
    nonzero = [round(float(x), 10) for x in eigs[eigs > GAP_TOL][:5]]
    lambda2 = float(eigs[1]) if len(eigs) > 1 else 0.0
    gap_anomaly = bool(abs(lambda2) < GAP_TOL)
    zero_mult = int(np.count_nonzero(eigs == 0.0))
    print("S2a eig_first5:", first5, "eig_nonzero_first5:", nonzero, "zero_mult:", zero_mult)

    # ---------- S2b: truncated SVD rank-k approximation of L0 ----------
    U, s, Vt = np.linalg.svd(L0)
    k = min(SVD_RANK, len(s))
    L0_k = (U[:, :k] * s[:k]) @ Vt[:k, :]
    norm_full = float(np.linalg.norm(L0, "fro"))
    eps = float(np.linalg.norm(L0 - L0_k, "fro") / norm_full) if norm_full > 0 else 0.0
    eps_exceeds = bool(eps > EPS_THRESHOLD)
    print(f"S2b svd_rank={k} eps={eps:.6f} (threshold {EPS_THRESHOLD})")

    # ---------- S3: residual verdict ----------
    reasons = []
    if eps_exceeds:
        reasons.append(f"epsilon {eps:.6f} > {EPS_THRESHOLD}")
    if gap_anomaly:
        reasons.append(f"lambda2 {lambda2:.3e} ~ 0 ({n_components} connected components)")
    residual = eps_exceeds or gap_anomaly

    rec = {
        "ts": args.ts,
        "lab": "chgs-lab",
        "type": "chgs_residual" if residual else "chgs_clean",
        "cases": {
            "s1_cc_build": {"status": "pass", "metrics": cc_stats},
            "s2_spectral_svd": {
                "status": "pass",
                "metrics": {
                    "eig_first5": first5,
                    "eig_nonzero_first5": nonzero,
                    "lambda2": round(lambda2, 12),
                    "zero_eig_multiplicity": zero_mult,
                    "svd_rank": k,
                    "epsilon": round(eps, 6),
                },
            },
        },
        "verdict": {
            "residual": residual,
            "reasons": reasons,
            "epsilon_threshold": EPS_THRESHOLD,
            "gap_tol": GAP_TOL,
        },
        "versions": {
            "numpy": importlib.metadata.version("numpy"),
            "networkx": importlib.metadata.version("networkx"),
            "toponetx": (importlib.metadata.version("toponetx")
                         if built["tnx"] == "ok" else built["tnx"]),
        },
    }
    rec["overall"] = "pass" if all(c["status"] == "pass" for c in rec["cases"].values()) else "fail"

    with open(args.out_jsonl, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    with open(args.out_summary, "w", encoding="utf-8") as f:
        json.dump(rec, f, indent=2, ensure_ascii=False)
    print(json.dumps(rec, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
