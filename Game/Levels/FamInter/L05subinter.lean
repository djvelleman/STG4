import Game.Levels.FamInter.L04interunion

open Set

namespace STG4

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
Statement (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ s ∈ F, A ⊆ s := by
  apply Iff.intro
  intro h1
  intro s h2
  intro x h3
  have h4 : x ∈ ⋂₀ F := h1 h3
  rewrite [mem_sInter] at h4
  exact h4 s h2
  Hint "Notice that the parentheses in the next goal are necessary, to indicate that the universal
  quantifier applies only to the subset statement.  Without the parentheses, Lean would interpret
  the universal quantifier as applying to the entire rest of the statement."
  intro h1
  intro x h2
  rewrite [mem_sInter]
  intro t h3
  have h4 : A ⊆ t := h1 t h3
  exact h4 h2
