apply Iff.intro
intro h s sF x xA
apply h xA
exact sF
intro h x xA s sF
apply h at sF
apply sF xA
