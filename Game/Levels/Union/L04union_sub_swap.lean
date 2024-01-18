import Game.Levels.Union.L03cases

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

LemmaTab "∩∪"

LemmaDoc union_sub_swap as "union_sub_swap" in "∩∪"
"For any sets `A` and `B`, `union_sub_swap A B` is a proof of
`A ∪ B ⊆ B ∪ A`."

/-- For any sets $A$ and $B$, $A \cup B \subseteq B \cup A$. -/
Statement union_sub_swap (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x h
  Hint (hidden := true) "It will help you see how to proceed if you
  write out the definition of union in both the assumption `{h}` and the goal."
  rewrite [union_def]
  rewrite [union_def] at h
  Hint (hidden := true) "The form of the assumption `{h}` now suggests proof by cases."
  cases' h with hA hB
  exact Or.inr hA
  exact Or.inl hB

Conclusion
"
You'll be able to use the theorem `union_sub_swap` in the next level to prove
that union is commutative.
"
