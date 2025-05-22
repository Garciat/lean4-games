apply one_le_of_ne_zero at ha
apply one_le_of_ne_zero at hb
cases ha
cases hb
rw [add_comm, one_eq_succ_zero, add_succ, add_zero] at h
rw [add_comm, one_eq_succ_zero, add_succ, add_zero] at h_1
rw [h, h_1, mul_succ, succ_mul, add_succ]
apply succ_ne_zero
