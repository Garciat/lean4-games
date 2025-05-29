obtain ⟨a, ⟨aF, h3⟩⟩ := h2
obtain ⟨b, ⟨bG, a_sub_b⟩⟩ := h1 a aF
have b_sub_a := h3 b bG
have a_eq_b := Subset.antisymm a_sub_b b_sub_a
have aFG := And.intro aF bG
rw [← a_eq_b] at aFG
use a
exact aFG
