#!/usr/bin/env python3
"""P4: encode/decode matrix properties over the toy field F2^8 (Z3).

Toy formalization of the wall-protocol orthogonality (vci-library
spec/wall-01 section 2): the key-derivation map is written as a linear map
over F2^n so the "encode/decode matrix" layer becomes machine-checkable.

Model (n=8):
    encode  E(s, r) = s ^ M*r        (s plaintext, r fresh randomness)
    derived key  K(r) = M*r          (simplified analog of vault K-derivation)
    decode  D(c, k) = c ^ k

M is a fixed full-rank 8x8 boolean matrix (upper-triangular all-ones,
det = 1 over F2, rank asserted at runtime).

P4a (positive, correctness):
    forall s, r: D(E(s,r), K(r)) = s.  Checked as negation -> UNSAT
    (equivalent to exhausting all 256x256 (s,r) inputs).

P4b (positive, orthogonality / bounded masking witness):
    For a fixed linear observation operator O (rank < n, no K component),
    ker(O*M) is nontrivial, so there exist r != r' whose observations
    collide for *every* plaintext s:
        O*E(s,r) = O*E(s,r')  (independent of s, since O*M*(r^r') = 0).
    Check: SAT, witness = collision pair (r, r', d = r^r').

P4c (control, no leak at full rank):
    A leak direction is a nonzero left-null vector o with o*M = 0
    (then o*E(s,r) = o*s deterministically, randomness-free leak).
    Full-rank M => no such o exists.  Check: UNSAT.

P4d (refutation, rank-deficient M leaks):
    With M' = M minus its last row (rank <= 7), a leak direction must
    exist.  Check: SAT, witness = leak vector o.

Exit 0 iff all four verdicts match expectations; witness lines are printed
with a stable prefix for the runner to harvest.
"""
import sys

import z3

N = 8

# full-rank 8x8 boolean matrix: upper-triangular all-ones (det = 1 over F2)
M_FULL = [sum(1 << j for j in range(i, N)) for i in range(N)]
# rank-deficient variant: last row zeroed (rank <= 7)
M_DEF = M_FULL[:-1] + [0]
# fixed observation operator: projection onto the low 4 bits (rank 4 < n)
O_PROJ = [1 << i for i in range(4)]


def gf2_rank(rows):
    rows = list(rows)
    rank = 0
    for col in range(N):
        piv = next((k for k in range(rank, len(rows)) if (rows[k] >> col) & 1), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for k in range(len(rows)):
            if k != rank and (rows[k] >> col) & 1:
                rows[k] ^= rows[rank]
        rank += 1
    return rank


def matvec(rows, x):
    """Boolean-matrix/vector product over F2; x is a BitVec(N)."""
    out = []
    for r in rows:
        bits = [z3.Extract(j, j, x) for j in range(N) if (r >> j) & 1]
        if bits:
            b = bits[0]
            for w in bits[1:]:
                b = b ^ w
        else:
            b = z3.BitVecVal(0, 1)
        out.append(b)
    res = out[0]
    for b in out[1:]:
        res = z3.Concat(b, res)
    return res


def encode(m_rows, s, r):
    return s ^ matvec(m_rows, r)


def decode(c, k):
    return c ^ k


def p4a_correctness():
    s, r = z3.BitVecs("p4a_s p4a_r", N)
    sol = z3.Solver()
    sol.add(decode(encode(M_FULL, s, r), matvec(M_FULL, r)) != s)
    res = sol.check()
    print(f"P4A_VERDICT={res}")
    if res != z3.unsat:
        print("P4A_UNEXPECTED: expected unsat (decode must invert encode)")
        if res == z3.sat:
            print(sol.model())
        return False
    print("P4A_DETAIL=D(E(s,r),K(r))=s for all s,r in F2^8 (256x256 inputs "
          "covered by quantified negation); negation UNSAT")
    return True


def p4b_masking_witness():
    r, r2 = z3.BitVecs("p4b_r p4b_r2", N)
    d = r ^ r2
    sol = z3.Solver()
    # collision in the observation map, independent of the plaintext:
    # O*M*(r ^ r') = 0  <=>  forall s: O*E(s,r) = O*E(s,r')
    sol.add(r != r2)
    sol.add(matvec(O_PROJ, matvec(M_FULL, d)) == 0)
    res = sol.check()
    print(f"P4B_VERDICT={res}")
    if res != z3.sat:
        print("P4B_UNEXPECTED: expected sat (nontrivial ker(O*M) witness)")
        return False
    m = sol.model()
    rv, r2v, dv = (m.eval(r), m.eval(r2), m.eval(d))
    # sanity: collision really holds for arbitrary s (spot-check two)
    s0, s1 = z3.BitVecVal(0x00, N), z3.BitVecVal(0xA5, N)
    lhs = [matvec(O_PROJ, encode(M_FULL, s0, rv)), matvec(O_PROJ, encode(M_FULL, s1, rv))]
    rhs = [matvec(O_PROJ, encode(M_FULL, s0, r2v)), matvec(O_PROJ, encode(M_FULL, s1, r2v))]
    chk = z3.Solver()
    chk.add(z3.Or(lhs[0] != rhs[0], lhs[1] != rhs[1]))
    assert chk.check() == z3.unsat, "witness does not collide"
    print(f"P4B_WITNESS=r={rv.as_long():#04x}, r'={r2v.as_long():#04x}, d=r^r'={dv.as_long():#04x} in "
          f"ker(O*M), O=proj4 (rank 4 < 8): O*E(s,r)=O*E(s,r') for every s "
          f"(spot-checked s=0x00,0xa5)")
    return True


def _leak_dir(m_rows):
    o = z3.BitVec("p4_o", N)
    sol = z3.Solver()
    sol.add(o != 0)
    # left null space: o*M = 0  <=>  M^T*o = 0
    mt = [sum(((m_rows[i] >> j) & 1) << i for i in range(N)) for j in range(N)]
    sol.add(matvec(mt, o) == 0)
    return sol, o


def p4c_no_leak_full_rank():
    sol, _ = _leak_dir(M_FULL)
    res = sol.check()
    print(f"P4C_VERDICT={res}")
    if res != z3.unsat:
        print("P4C_UNEXPECTED: expected unsat (full-rank M has no leak direction)")
        return False
    print("P4C_DETAIL=full-rank M (rank 8): no nonzero o with o*M=0; "
          "randomness-free observation leak impossible; UNSAT")
    return True


def p4d_leak_rank_deficient():
    sol, o = _leak_dir(M_DEF)
    res = sol.check()
    print(f"P4D_VERDICT={res}")
    if res != z3.sat:
        print("P4D_UNEXPECTED: expected sat (rank-deficient M must leak)")
        return False
    m = sol.model()
    ov = m.eval(o)
    print(f"P4D_WITNESS=o={ov.as_long():#04x} != 0 with o*M'=0 (rank(M')={gf2_rank(M_DEF)} "
          f"< 8): observation o*E(s,r)=o*s leaks plaintext bits independent of r")
    return True


if __name__ == "__main__":
    assert gf2_rank(M_FULL) == N, "M_FULL must be full rank"
    assert gf2_rank(M_DEF) < N, "M_DEF must be rank deficient"
    assert gf2_rank(O_PROJ) < N, "O must have rank < n"
    ok = all([p4a_correctness(), p4b_masking_witness(),
              p4c_no_leak_full_rank(), p4d_leak_rank_deficient()])
    print(f"P4_VERSION={z3.get_version_string()}")
    sys.exit(0 if ok else 1)
