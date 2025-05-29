intro x
intro h
rewrite [mem_union]
rewrite [mem_union] at h
rcases h
exact Or.inr h
exact Or.inl h
