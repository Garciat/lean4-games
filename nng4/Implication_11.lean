intro
repeat rw [add_succ, succ_add] at h
repeat rw [← add_succ, ← succ_add] at h
repeat rw [add_succ, succ_add] at a
rw [add_zero] at a
repeat apply succ_inj at a
apply zero_ne_succ at a
exact a
