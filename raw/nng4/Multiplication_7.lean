induction c
rw [add_zero, mul_zero, add_zero]
rfl
rw [add_succ, mul_succ, n_ih, mul_succ, add_assoc]
rfl
