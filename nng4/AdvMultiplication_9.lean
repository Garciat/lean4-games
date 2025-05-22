induction b with d hd generalizing c
rw [mul_zero] at h
symm at h
apply mul_eq_zero at h
cases h
tauto
tauto
cases c with e
rw [mul_zero] at h
have : succ d ≠ 0
apply succ_ne_zero
apply mul_ne_zero at h
trivial
exact ha
exact this
simp
rw [mul_succ, mul_succ] at h
apply add_right_cancel at h
apply hd at h
exact h
