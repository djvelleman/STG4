import Game.Levels.FamUnion.L05unionunion

open Set

namespace STG4

variable {U : Type}

World "FamUnion"
Level 6
Title "Union subset of a set"

Introduction
"
Suppose `A` is a set and `F` is a family of sets.  In this level you'll determine the conditions
under which `⋃₀ F` is a subset of `A`.
"

/-- Suppose $A$ is a set and $F$ is a family of sets.  Then $\bigcup F$ is a subset of $A$
if and only if every element of $F$ is a subset of $A$. -/
Statement (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  apply Iff.intro
  intro h1
  intro s h2
  intro x h3
  Hint (hidden := true) "Notice that `{h1}` could be applied to a proof of `{x} ∈ ⋃₀ F` to
  prove the goal.  That means that `apply {h1}` will set `{x} ∈ ⋃₀ F` as the goal."
  apply h1
  rewrite [mem_sUnion]
  use s
  intro h1
  intro x h2
  rewrite [mem_sUnion] at h2
  obtain ⟨s, hs⟩ := h2
  exact h1 s hs.left hs.right
