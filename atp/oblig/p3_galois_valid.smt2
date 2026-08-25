; P3-positive: Galois connection between a 4-state obligation chain and a
; 4-state evidence chain. alpha is the lower adjoint, gamma the upper adjoint:
;   alpha(o) = o div 2          (evidence strength demanded by obligation o)
;   gamma(e) = min(3, 2*e + 1)  (weakest obligation that evidence e discharges)
; Galois axiom:  o <= gamma(e)  <=>  alpha(o) <= e   for all o,e in {0,1,2,3}.
; A violating pair is asserted to exist; expected verdict: unsat (axiom holds).
(set-option :produce-models true)
(set-logic QF_LIA)
(define-fun alpha ((o Int)) Int (div o 2))
(define-fun gamma ((e Int)) Int (ite (<= (+ (* 2 e) 1) 3) (+ (* 2 e) 1) 3))
(define-fun gc ((o Int) (e Int)) Bool
  (= (<= o (gamma e)) (<= (alpha o) e)))
(declare-fun o () Int)
(declare-fun e () Int)
(assert (and (<= 0 o) (<= o 3)))
(assert (and (<= 0 e) (<= e 3)))
(assert (not (gc o e)))
(check-sat)
(get-value (o e))
