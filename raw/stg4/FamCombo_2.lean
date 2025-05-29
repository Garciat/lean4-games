ext x
apply Iff.intro
intro h1
rw [mem_sUnion]
rw [mem_compl_iff, mem_sInter] at h1
push_neg at h1
obtain ⟨s, ⟨sF, xns⟩⟩ := h1
use sᶜ
rw [mem_setOf, compl_compl]
exact And.intro sF xns
intro h1 h2
rewrite [mem_sUnion] at h1
rewrite [mem_sInter] at h2
obtain ⟨s, ⟨scF, xs⟩⟩ := h1
rewrite [mem_setOf] at scF
apply h2 at scF
exact scF xs
