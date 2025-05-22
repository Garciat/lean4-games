ext x
rw [mem_union, mem_inter_iff, mem_inter_iff, mem_union, mem_inter_iff]
constructor
intro h
rcases h
rcases right
left
exact And.intro left h
right
exact And.intro left h
intro h
apply And.intro
rcases h
exact h.left
exact h.left
rcases h
exact Or.inl h.right
exact Or.inr h.right
