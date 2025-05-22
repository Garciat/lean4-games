intro h
induction n with h ih
repeat rw [add_zero] at h
exact h
repeat rw [add_succ] at h
apply succ_inj at h
apply ih at h
exact h
