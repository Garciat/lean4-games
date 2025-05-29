apply Iff.intro
intro h
apply compl_subset_compl_of_subset
exact h
intro h
apply compl_subset_compl_of_subset at h
rewrite [compl_compl, compl_compl] at h
exact h
