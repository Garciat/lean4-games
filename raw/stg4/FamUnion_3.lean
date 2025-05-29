intro x xUF
rw [mem_sUnion]
rw [mem_sUnion] at xUF
obtain ⟨s, hs⟩ := xUF
use s
exact And.intro (h1 hs.left) hs.right
