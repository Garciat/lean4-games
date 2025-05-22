intro x
intro h
have h3 : x ∈ A ∪ C := by exact Or.inl h
apply h1 at h3
rcases h3
exact h_1
have h4 : x ∈ A ∩ C := by exact And.intro h h_1
apply h2 at h4
exact h4.left
