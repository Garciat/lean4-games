import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Order.BooleanAlgebra

-- Level 1
example {U} (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {s | sᶜ ∈ F} := by
  ext x
  apply Iff.intro
  · intro h t ts
    by_contra xnt
    exact h (Exists.intro tᶜ (And.intro ts xnt))
  · intro h1 ⟨f, ⟨f_in_F, x_in_f⟩⟩
    have h2 := h1 fᶜ
    rw [Set.mem_setOf, compl_compl] at h2
    exact h2 f_in_F x_in_f

-- Level 2
example {U} (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {s | sᶜ ∈ F} := by
  ext x

  rw [Set.mem_compl_iff, Set.mem_sInter, Set.mem_sUnion]
  push_neg
  apply Iff.intro
  · intro ⟨s, ⟨s_in_F, x_nin_s⟩⟩
    use sᶜ
    rw [Set.mem_setOf, compl_compl]
    exact And.intro s_in_F x_nin_s
  · intro ⟨s, ⟨sc_in_F, x_in_s⟩⟩
    by_contra h
    push_neg at h
    apply h sᶜ sc_in_F x_in_s

-- Level 3
example {U} (F G : Set (Set U)) (h1 : ∀ s ∈ F, ∃ t ∈ G, s ⊆ t) (h2 : ∃ s ∈ F, ∀ t ∈ G, t ⊆ s) : ∃ u, u ∈ F ∩ G := by
  obtain ⟨a, ⟨a_in_F, h3⟩⟩ := h2
  obtain ⟨b, ⟨b_in_G, a_sub_b⟩⟩ := h1 a a_in_F
  have a_eq_b := Set.Subset.antisymm a_sub_b (h3 b b_in_G)
  have aFG := And.intro a_in_F b_in_G
  rw [← a_eq_b] at aFG
  use a
  exact aFG

-- Level 4
example {U} (F G H : Set (Set U)) (h1 : ∀ s ∈ F, ∃ u ∈ G, s ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x ⟨⟨a, ⟨a_in_F, x_in_a⟩⟩, h2⟩
  obtain ⟨b, ⟨b_in_G, a_inter_b_in_H⟩⟩ := h1 a a_in_F
  obtain x_in_b := h2 b b_in_G
  use a ∩ b
  exact And.intro a_inter_b_in_H (And.intro x_in_a x_in_b)

-- Level 5
example {U} (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x ⟨⟨a, a_in_F, x_in_a⟩, x_in_UGc⟩
  rw [Set.mem_sUnion]
  rw [Set.mem_compl_iff, Set.mem_sUnion] at x_in_UGc
  push_neg at x_in_UGc
  by_contra h2
  push_neg at h2
  by_cases h : a ∈ G
  · exact x_in_UGc a h x_in_a
  · exact h2 a (And.intro a_in_F h) x_in_a

-- Level 6
example {U} (F G : Set (Set U)) (h1 : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) : (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  intro x ⟨⟨a, ⟨a_in_F, x_in_a⟩⟩, ⟨b, ⟨b_in_G, x_in_b⟩⟩⟩
  rw [Set.mem_sUnion]
  by_cases h : a ∈ G
  · exact Exists.intro a (And.intro (And.intro a_in_F h) x_in_a)
  · have ⟨h2, h3⟩ := h1 (Exists.intro a (And.intro (And.intro a_in_F h) x_in_a))
    rw [Set.mem_sUnion] at h2
    rw [Set.mem_compl_iff, Set.mem_sUnion] at h3
    push_neg at h3
    obtain ⟨c, ⟨c_in_F, x_in_c⟩⟩ := h2
    by_contra
    exact h3 b b_in_G x_in_b

-- Level 7
example {U} (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ vᶜ} := by
  intro x ⟨⟨a, ⟨a_in_F, x_in_a⟩⟩, h⟩
  rw [Set.mem_sUnion]

  rw [Set.mem_compl_iff, Set.mem_sInter] at h
  push_neg at h
  obtain ⟨b, ⟨b_in_G, x_in_b⟩⟩ := h

  use a ∩ bᶜ
  rw [Set.mem_setOf]

  apply And.intro
  · use a
    apply And.intro
    · exact a_in_F
    · use b
  · exact And.intro x_in_a x_in_b

-- Level 8
example {U} (A : Set U) (h1 : ∀ F, (⋃₀ F = A → A ∈ F)) : ∃ x, A = {x} := by
  let p : Set (Set U) := {s | ∃ x ∈ A, s = {x}}

  have h2 : ⋃₀ p = A := by
    ext x
    rw [Set.mem_sUnion]
    apply Iff.intro
    · intro ⟨a, ⟨⟨y, ⟨y_in_A, a_eq_y⟩⟩, x_in_a⟩⟩
      rw [a_eq_y] at x_in_a
      rw [← x_in_a] at y_in_A
      exact y_in_A
    · intro x_in_a
      use {x}
      constructor
      · use x
      · rfl

  obtain ⟨x, ⟨⟩⟩ := h1 p h2
  use x
