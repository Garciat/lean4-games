intro x h2
obtain ⟨⟨a, ⟨a_in_F, x_in_a⟩⟩, ⟨b, ⟨b_in_G, x_in_b⟩⟩⟩ := h2
rw [mem_sUnion]
by_cases h3 : a ∈ G
exact Exists.intro a (And.intro (And.intro a_in_F h3) x_in_a)
have ⟨h5, h6⟩ := h1 (Exists.intro a (And.intro (And.intro a_in_F h3) x_in_a))
rw [mem_sUnion] at h5
rw [mem_compl_iff, mem_sUnion] at h6
push_neg at h6
obtain ⟨c, ⟨c_in_F, x_in_c⟩⟩ := h5
by_contra h7
have h8 := h6 b b_in_G
exact h8 x_in_b
