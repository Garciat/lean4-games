apply eq_succ_of_ne_zero at ha
cases ha
use w
rw [h, add_comm, one_eq_succ_zero, add_succ, add_zero]
rfl
