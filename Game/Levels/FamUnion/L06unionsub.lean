import Game.Levels.FamUnion.L05unionunion

variable {U : Type}

World "FamUnion"
Level 6
Title "Union Subset of a Set"

Introduction
"
Suppose `A` is a set and `F` is a family of sets.  In this level you'll determine the conditions
under which `⋃₀ F` is a subset of `A`.
"

/-- Suppose $A$ is a set and $F$ is a family of sets.  Then $\bigcup F$ is a subset of $A$
if and only if every element of $F$ is a subset of $A$. -/
Statement (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ B ∈ F, B ⊆ A := by
  apply Iff.intro
  intro h1
  intro B h2
  intro x h3
  Hint (hidden := true) "Notice that `{h1}` could be applied to a proof of `{x} ∈ ⋃₀ F` to
  prove the goal.  That means that `apply {h1}` will set `{x} ∈ ⋃₀ F` as the goal."
  apply h1
  rewrite [fam_union_def]
  use B
  intro h1
  intro x h2
  rewrite [fam_union_def] at h2
  cases' h2 with B h2
  exact h1 B h2.left h2.right
