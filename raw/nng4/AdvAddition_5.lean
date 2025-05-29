cases b with d
rw [add_zero]
intro h
exact h
intro h
rw [  add_succ] at h
apply succ_ne_zero at h
cases h
