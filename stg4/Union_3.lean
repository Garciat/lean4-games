intro x
intro h3
rewrite [mem_union] at h3
rcases h3 with h3A | h3B
exact h1 h3A
exact h2 h3B
