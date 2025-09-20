import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Union"
Level 4
Title "Union subset of swap"

Introduction
"
In the next level we're going to prove that union is commutative; that is,
`A ∪ B = B ∪ A`.  We're going to imitate the approach we used in Intersection World
to prove that intersection is commutative.  We begin by proving `A ∪ B ⊆ B ∪ A`.
"

TheoremTab "∩∪"

/-- For any sets `A` and `B`, `union_sub_swap A B` is a proof of
`A ∪ B ⊆ B ∪ A`. -/
TheoremDoc STG4.union_subset_swap as "union_subset_swap" in "∩∪"

/-- For any sets $A$ and $B$, $A \cup B \subseteq B \cup A$. -/
Statement union_subset_swap (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x h
  Hint (hidden := true) "It will help you see how to proceed if you
  write out the definition of union in both the assumption `{h}` and the goal."
  rewrite [mem_union]
  rewrite [mem_union] at h
  Hint (hidden := true) "The form of the assumption `{h}` now suggests proof by cases."
  rcases h with hA | hB
  exact Or.inr hA
  exact Or.inl hB

Conclusion
"
You'll be able to use the theorem `union_subset_swap` in the next level to prove
that union is commutative.
"
