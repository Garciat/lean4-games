induction x with a ha
induction y with b hb
left
apply le_refl
left
apply zero_le
cases ha
cases h
cases w
rw [add_zero] at h_1
right
rw [h_1]
apply le_succ_self
left
use a_1
rw [add_comm, add_succ]
rw [add_succ] at h_1
rw [add_comm]
exact h_1
cases h
cases w
rw [add_zero] at h_1
right
rw [h_1]
apply le_succ_self
cases y
right
apply zero_le
right
use succ (succ a_1)
rw [h_1]
rw [← add_succ]
rfl
