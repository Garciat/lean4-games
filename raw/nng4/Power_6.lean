induction m
rw [zero_add, pow_zero, one_mul]
rfl
rw [succ_add, pow_succ, n_ih, pow_succ, mul_assoc, mul_comm (a^n), ← mul_assoc]
rfl
