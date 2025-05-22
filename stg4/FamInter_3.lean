have s : A ∈ {A, B} ∧ B ∈ {A, B}
rw [mem_pair, mem_pair]
exact And.intro (Or.inl rfl) (Or.inr rfl)
ext x
rw [mem_sInter]
apply Iff.intro
intro h t m
rcases m with mA|mB
rw [mA]
exact h.left
rw [mB]
exact h.right
intro h
exact And.intro (h A s.left) (h B s.right)
