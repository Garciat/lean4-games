ext x
apply Iff.intro
intro h t ts
by_contra xnt
exact h (Exists.intro tᶜ (And.intro ts xnt))
intro h1 h2
rw [mem_sInter] at h1
obtain ⟨f, ⟨fF, xf⟩⟩ := h2
have h2 := h1 fᶜ
rw [mem_setOf, compl_compl] at h2
have h3 := h2 fF
exact h3 xf
