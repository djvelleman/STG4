import Game.Levels.FamCombo.L03threefam

variable {U : Type}

World "FamCombo"
Level 4
Title "A union intersected with the complement of another is a subset"

Introduction
"
What happens if you intersect `⋃₀ F` with `(⋃₀ G)ᶜ`, for two families `F` and `G`?
"

/-- Suppose $F$ and $G$ are families of sets.  Then $(\bigcup F) \cap (\bigcup G)^c \subseteq
\bigcup (F \cap G^c)$.-/
Statement (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x h1
  rewrite [inter_def] at h1
  have h1l := h1.left
  rewrite [fam_union_def] at h1l
  obtain ⟨S, hS⟩ := h1l
  rewrite [fam_union_def]
  use S
  apply And.intro
  rewrite [inter_def]
  apply And.intro
  exact hS.left
  rewrite [comp_def]
  by_contra h2
  have h1r := h1.right
  rewrite [comp_def, fam_union_def] at h1r
  push_neg at h1r
  have hnS := h1r S h2
  exact hnS hS.right
  exact hS.right
