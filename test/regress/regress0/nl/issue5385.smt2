; EXPECT: sat
(set-logic QF_NIRA)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun i5 () Int)
(assert (= r1 (- (* r3 r1 r1 r2 r1) 83123.0 r3)))
(declare-fun r12 () Real)
(check-sat)