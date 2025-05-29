intro x
intro h2
rewrite [mem_compl_iff]
rewrite [mem_compl_iff] at h2
by_contra
have : x ∈ B
exact h1 a
exact h2 this
