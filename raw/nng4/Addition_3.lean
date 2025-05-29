induction b with d dh
rw [add_zero, zero_add]
rfl
rw [add_succ]
induction a with t th
rw [add_zero, zero_add]
rfl
rw [dh]
rw [← add_succ]
rw [add_succ]
rw [add_succ]
rw [← add_succ]
rw [add_succ]
rw [add_succ]
rw [succ_add]
rfl
