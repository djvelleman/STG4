import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Intersection"
Level 6
Title "Intersection subset of swap"

Introduction
"
In the next level we're going to prove that intersection is commutative; that is,
`A ∩ B = B ∩ A`.  As a warm-up, in this level we prove `A ∩ B ⊆ B ∩ A`.
"

TheoremTab "∩∪"

/-- For any sets `A` and `B`, `inter_subset_swap A B` is a proof of
`A ∩ B ⊆ B ∩ A`. -/
TheoremDoc STG4.inter_subset_swap as "inter_subset_swap" in "∩∪"

/-- For any sets $A$ and $B$, $A \cap B \subseteq B \cap A$. -/
Statement inter_subset_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x h
  Hint (hidden := true) "It will help you see how to proceed if you
  write out the definition of intersection in both the assumption {h} and the goal.
  Using the `rewrite` tactic isn't necessary; you can just do the rewriting in
  your head rather than asking Lean to do it.  But if it helps you to figure out the
  proof, go ahead and use the `rewrite` tactic."
  rewrite [mem_inter_iff]
  rewrite [mem_inter_iff] at h
  Hint (hidden := true) "Now `And.intro {h}.right {h}.left` proves the goal."
  exact And.intro h.right h.left

Conclusion
"
We have given this theorem the name `inter_subset_swap`.  Thus, from now on, for
any sets `A` and `B`, `inter_subset_swap A B` is a proof of `A ∩ B ⊆ B ∩ A`.
"
