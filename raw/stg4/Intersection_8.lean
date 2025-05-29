ext x
apply Iff.intro
intro h
exact And.intro (h.left.left) (And.intro (h.left.right) (h.right))
intro h
exact And.intro (And.intro h.left (h.right.left)) (h.right.right)
