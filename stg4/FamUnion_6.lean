apply Iff.intro
intro h s sF x xs
apply h
rw [mem_sUnion]
use s
intro h x xUF
obtain ⟨s, ⟨sF, xs⟩ ⟩ := xUF
exact h s sF xs
