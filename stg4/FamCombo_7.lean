intro x h1
obtain ⟨⟨a, ⟨a_in_F, x_in_a⟩⟩, h3⟩ := h1
rw [mem_compl_iff, mem_sInter] at h3
rw [mem_sUnion]
push_neg at h3
obtain ⟨b, ⟨b_in_G, x_in_b⟩⟩ := h3
use a ∩ bᶜ 
rw [mem_setOf]
apply And.intro
use a
apply And.intro
exact a_in_F
use b
exact And.intro x_in_a x_in_b
