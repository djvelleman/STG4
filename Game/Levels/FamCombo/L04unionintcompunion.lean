import Game.Levels.FamCombo.L03threefam

variable {U : Type}

World "FamCombo"
Level 4
Title "A union intersected with the complement of another"

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
  cases' h1l with S hS
  rewrite [fam_union_def]
  use S
  apply And.intro
  rewrite [inter_def]
  apply And.intro
  exact hS.left
  rewrite [comp_def]
  by_contra h2
  have h1r := h1.right
  rewrite [comp_def] at h1r
  apply h1r
  rewrite [fam_union_def]
  use S
  exact And.intro h2 hS.right
  exact hS.right
