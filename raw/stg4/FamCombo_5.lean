intro x h1
obtain ⟨⟨a, a_in_F, x_in_a⟩, x_in_UGc⟩ := h1
rw [mem_sUnion]
rw [mem_compl_iff, mem_sUnion] at x_in_UGc
push_neg at x_in_UGc
by_contra h2
push_neg at h2
by_cases h : a ∈ G
exact x_in_UGc a h x_in_a
exact h2 a (And.intro a_in_F h) x_in_a
