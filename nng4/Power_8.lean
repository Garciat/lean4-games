induction n
rw [pow_zero, mul_zero, pow_zero]
rfl
rw [pow_succ, mul_succ, pow_add, n_ih]
rfl
