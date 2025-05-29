ext x
apply Iff.intro
intro h
rewrite [mem_union, mem_union] at h
rewrite [mem_union, mem_union]
rcases h
rcases h
left
exact h
right
left
exact h
right
right
exact h
intro h
rewrite [mem_union, mem_union] at h
rewrite [mem_union, mem_union]
rcases h
left
left
exact h
rcases h
left
right
exact h
right
exact h
