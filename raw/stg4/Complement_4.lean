apply Subset.antisymm
intro x
intro h
rewrite [mem_compl_iff, mem_compl_iff] at h
push_neg at h
exact h
intro x
intro h
rewrite [mem_compl_iff, mem_compl_iff] 
push_neg
exact h
