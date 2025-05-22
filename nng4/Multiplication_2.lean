induction m
apply mul_zero
rw [mul_succ, n_ih, zero_add]
rfl
