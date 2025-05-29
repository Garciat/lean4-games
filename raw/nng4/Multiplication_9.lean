induction c
repeat rw [mul_zero]
rfl
repeat rw [mul_succ]
rw [n_ih, ← mul_add]
rfl
