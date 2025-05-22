intro x h
rw [mem_sInter] at h
rw [mem_union, mem_sInter]
by_cases xA : x ∈ A
left
exact xA
right
intro t tF
apply h1 at tF
apply h at tF
rw [mem_union] at tF
rcases tF 
by_contra
exact xA h_1
exact h_1
