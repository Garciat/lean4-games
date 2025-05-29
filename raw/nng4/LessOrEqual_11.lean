cases x
left
rfl
rw [two_eq_succ_one] at hx
apply succ_le_succ at hx
apply le_one at hx
cases hx
right
left
rw [h]
decide
right
right
rw [h]
decide
