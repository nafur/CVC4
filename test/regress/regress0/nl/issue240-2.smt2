; EXPECT: sat
(set-logic QF_NRA)
(declare-const r0 Real)
(declare-const r1 Real)
(declare-const r5 Real)
(declare-const r7 Real)
(declare-const r11 Real)
(assert (= r0 (* r7 r5) 0.03310006 r11 r1))
(check-sat)