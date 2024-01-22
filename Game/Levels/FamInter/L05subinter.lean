import Game.Levels.FamInter.L04interunion

variable {U : Type}

World "FamInter"
Level 5
Title "Subset of an intersection"

Introduction
"
If `A` is a set and `F` is a family of sets, under what circumstances is it the case
that `A ⊆ ⋂₀ F`?  In this level you'll discover the answer to that question.
"

/-- Suppose $A$ is a set and $F$ is a family of sets.  Then $A$ is a subset of $\bigcap F$ if
and only if $A$ is a subset of every element of $F$.-/
Statement (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ B ∈ F, A ⊆ B := by
  apply Iff.intro
  intro h1
  intro B h2
  intro x h3
  have h4 : x ∈ ⋂₀ F := h1 h3
  rewrite [fam_inter_def] at h4
  exact h4 B h2
  Hint "Notice that the parentheses in the next goal are necessary, to indicate that the universal
  quantifier applies only to the subset statement.  Without the parentheses, Lean would interpret
  the universal quantifier as applying to the entire rest of the statement."
  intro h1
  intro x h2
  rewrite [fam_inter_def]
  intro S h3
  have h4 : A ⊆ S := h1 S h3
  exact h4 h2
