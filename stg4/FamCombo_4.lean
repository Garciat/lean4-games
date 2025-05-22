intro x h2
obtain ⟨h3, h4⟩ := h2
obtain ⟨a, ⟨a_in_F, x_in_a⟩⟩ := h3
obtain ⟨b, ⟨b_in_G, a_inter_b_in_H⟩⟩ := h1 a a_in_F
obtain x_in_b := h4 b b_in_G
use a ∩ b
exact And.intro a_inter_b_in_H (And.intro x_in_a x_in_b)
