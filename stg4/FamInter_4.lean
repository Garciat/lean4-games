ext x
rw [mem_sInter, mem_inter_iff, mem_sInter, mem_sInter]
apply Iff.intro
intro h
apply And.intro
intro t tF
apply h t (Or.inl tF)
intro t tG
apply h t (Or.inr tG)
intro h t tFG
rcases tFG with tF|tG
apply h.left t tF
apply h.right t tG
