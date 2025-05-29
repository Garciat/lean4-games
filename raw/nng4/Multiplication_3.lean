induction b
rw [mul_zero, mul_zero, add_zero]
rfl
rw [mul_succ, mul_succ, n_ih, add_succ, add_succ, add_assoc, add_comm n a, add_assoc]
rfl
