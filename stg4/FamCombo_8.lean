have h2 := h1 {s | ∃ x ∈ A, s = {x}}
have h3 : ⋃₀ {s | ∃ x ∈ A, s = {x}} = A

ext x
rw [mem_sUnion]
apply Iff.intro

intro h
obtain ⟨a, ⟨⟨y, ⟨y_in_A, a_eq_y⟩⟩, x_in_a⟩⟩ := h
rw [a_eq_y] at x_in_a
rw [← x_in_a] at y_in_A
exact y_in_A

intro x_in_A
use {x}
rw [mem_setOf]
apply And.intro
use x
rfl

have h := h2 h3
obtain ⟨x, ⟨⟩⟩ := h
use x
