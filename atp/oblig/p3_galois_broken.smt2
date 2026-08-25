; P3-control: same obligation/evidence chains, but with a deliberately broken
; upper adjoint gamma_wrong(e) = min(3, 2*e). The Galois axiom must FAIL;
; expected verdict: sat with a concrete witness pair (o,e) violating
;   o <= gamma_wrong(e)  <=>  alpha(o) <= e.
; (Dual discipline: the valid adjoint in p3_galois_valid.smt2 yields unsat.)
(set-option :produce-models true)
(set-logic QF_LIA)
(define-fun alpha ((o Int)) Int (div o 2))
(define-fun gamma_wrong ((e Int)) Int (ite (<= (* 2 e) 3) (* 2 e) 3))
(define-fun gc ((o Int) (e Int)) Bool
  (= (<= o (gamma_wrong e)) (<= (alpha o) e)))
(declare-fun o () Int)
(declare-fun e () Int)
(assert (and (<= 0 o) (<= o 3)))
(assert (and (<= 0 e) (<= e 3)))
(assert (not (gc o e)))
(check-sat)
(get-value (o e))
