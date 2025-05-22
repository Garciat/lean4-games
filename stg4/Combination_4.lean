rw [← compl_compl (A ∪ (B ∩ C))]
rw [compl_union, compl_inter B C]
rw [inter_distrib_left]
rw [← compl_union, ← compl_union, ← compl_inter, compl_compl]
