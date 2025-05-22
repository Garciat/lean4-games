induction n
repeat rw [pow_zero]
rw [mul_one]
rfl
repeat rw [pow_succ]
rw [n_ih, mul_assoc, mul_assoc]
rw [mul_comm (b ^ n_1), mul_comm (b ^ n_1), mul_assoc]
rfl
