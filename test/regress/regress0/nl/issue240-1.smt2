; EXPECT: sat
(set-logic QF_NRA)
(declare-fun _substvar_45_ () Real)
(declare-const r0 Real)
(declare-const r2 Real)
(assert (> (/ (+ 758.33 r2 r2 r0) _substvar_45_) 9183098.0 r2))
(check-sat)
