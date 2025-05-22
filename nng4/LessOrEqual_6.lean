cases hxy with a ha
cases hyx with b hb
rw [ha] at hb
nth_rewrite 1 [← add_zero x] at hb
rw [add_assoc] at hb
apply add_left_cancel at hb
symm at hb
apply add_right_eq_zero at hb
rw [hb] at ha
simp at ha
symm
exact ha
