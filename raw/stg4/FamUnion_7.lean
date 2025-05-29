ext x
apply Iff.intro
intro h
rw [mem_inter_iff, mem_sUnion] at h
obtain ⟨xA, ⟨b, ⟨bF, xb⟩⟩⟩ := h
rw [mem_sUnion]
use (A ∩ b)
apply And.intro
rw [mem_setOf]
use b
exact And.intro xA xb
intro h
rw [mem_sUnion] at h
obtain ⟨a, ⟨⟨b, ⟨bF, aAb⟩⟩, xa⟩⟩ := h
rw [aAb] at xa
rw [mem_inter_iff, mem_sUnion]
apply And.intro
exact xa.left
use b
apply And.intro
exact bF
exact xa.right
