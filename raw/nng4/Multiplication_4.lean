induction b
rw [zero_mul, mul_zero]
rfl
rw [succ_mul, mul_succ, n_ih]
rfl
