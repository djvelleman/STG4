import Game.Levels.FamCombo.L05unionintunion

variable {U : Type}

World "FamCombo"
Level 6
Title "A union intersected with the complement of an intersection"

Introduction
"
This time we'll study the intersection of `(⋃₀ F)` and `(⋂₀ G)ᶜ`.
"

/-- Suppose $F$ and $G$ are families of sets.  Then $(\bigcup F) \cap (\bigcap G)^c \subseteq
\bigcup \{S \mid \exists A \in F, \exists B \in G, S = A \cap B^c\}$.-/
Statement (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {S | ∃ A ∈ F, ∃ B ∈ G, S = A ∩ Bᶜ} := by
  intro x h1
  have h1l := h1.left
  have h1r := h1.right
  rewrite [fam_union_def] at h1l
  obtain ⟨A, hA⟩ := h1l
  rewrite [comp_def, fam_inter_def] at h1r
  push_neg at h1r
  obtain ⟨B, hB⟩ := h1r
  rewrite [fam_union_def]
  use A ∩ Bᶜ
  apply And.intro
  rewrite [set_builder_def]
  use A
  apply And.intro
  exact hA.left
  use B
  apply And.intro
  exact hB.left
  rfl
  rewrite [inter_def, comp_def]
  exact And.intro hA.right hB.right
