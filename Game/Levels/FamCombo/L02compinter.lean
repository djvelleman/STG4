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
    Hint (strict := true) "What statement would you like to contradict to complete the proof?  As
    in the last level, you can use `apply` to set a goal to achieve a contradiction."
    apply h1
    rewrite [fam_inter_def]
    intro S h3
    by_contra h4
    Hint "Now what statement would you like to contradict to complete the proof?"
  by_contra h2
  Hint (strict := true) "What statement would you like to contradict to complete the proof?  As
    in the last level, you can use `apply` to set a goal to achieve a contradiction."
  apply h1
  rewrite [fam_inter_def]
  intro S h3
  by_contra h4
  Hint "Now what statement would you like to contradict to complete the proof?"
  apply h2
  use Sᶜ
  apply And.intro
  rewrite [set_builder_def]
  rewrite [comp_comp]
  exact h3
  exact h4
  intro h1
  rewrite [comp_def]
  by_contra h2
  cases' h1 with S hS
  have hSl := hS.left
  rewrite [set_builder_def] at hSl
  rewrite [fam_inter_def] at h2
  have h3 := h2 Sᶜ hSl
  exact h3 hS.right
