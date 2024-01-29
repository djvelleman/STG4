import Game.Levels.FamCombo.L01compunion

variable {U : Type}

World "FamCombo"
Level 2
Title "Complement of a family intersection"

Introduction
"
Perhaps you have already guessed that there is a theorem about the complement
of an intersection of a family that is similar to the theorem in the last level.
"

/-- For any family of sets $F$, $(\bigcap F)^c = \bigcup \{A \mid A^c \in F\}$. -/
Statement (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {A | Aᶜ ∈ F} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [comp_def] at h1
  Branch
    rewrite [fam_union_def]
    by_contra h2
    Hint (strict := true) "What statement would you like to contradict to complete the proof?"
    apply h1
    rewrite [fam_inter_def]
    intro S h3
    by_contra h4
    Hint "Now what statement would you like to contradict to complete the proof?"
  Branch
    by_contra h2
    Hint (strict := true) "What statement would you like to contradict to complete the proof?"
    apply h1
    rewrite [fam_inter_def]
    intro S h3
    by_contra h4
    Hint "Now what statement would you like to contradict to complete the proof?"
  rewrite [fam_inter_def] at h1
  push_neg at h1
  obtain ⟨S, hS⟩ := h1
  use Sᶜ
  rewrite [set_builder_def, comp_comp, comp_def]
  exact hS
  intro h1
  rewrite [comp_def, fam_inter_def]
  push_neg
  rewrite [fam_union_def] at h1
  obtain ⟨S, hS⟩ := h1
  use Sᶜ
  apply And.intro
  rewrite [set_builder_def] at hS
  exact hS.left
  rewrite [comp_def]
  push_neg
  exact hS.right
