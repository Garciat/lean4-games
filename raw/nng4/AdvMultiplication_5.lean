apply mul_left_ne_zero at h
apply one_le_of_ne_zero at h
apply mul_le_mul_right 1 b a at h
rw [one_mul, mul_comm] at h
exact h
