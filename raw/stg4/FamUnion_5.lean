ext x
rw [mem_union, mem_sUnion, mem_sUnion, mem_sUnion]
apply Iff.intro
intro h
obtain ⟨s, ⟨sFUG, xs⟩⟩ := h
rcases sFUG
left
use s
right
use s
intro h
rcases h
obtain ⟨s, ⟨sF, xs⟩⟩ := h
use s
exact And.intro (Or.inl sF) xs
obtain ⟨s, ⟨sG, xs⟩⟩ := h
use s
exact And.intro (Or.inr sG) xs
