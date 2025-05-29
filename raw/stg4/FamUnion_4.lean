have s : A ∈ {A, B} ∧ B ∈ {A, B}
rw [mem_pair, mem_pair]
exact And.intro (Or.inl rfl) (Or.inr rfl)
ext x
apply Iff.intro
intro xAUB
rw [mem_sUnion]
rcases xAUB
exact Exists.intro A (And.intro s.left h)
exact Exists.intro B (And.intro s.right h)
intro h
rw [mem_sUnion] at h
obtain ⟨w, dw⟩ := h
rw [mem_union]
rw [mem_pair] at dw
rcases dw
rcases left
rw [h] at right
left
exact right
rw [h] at right
right
exact right
