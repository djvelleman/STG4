import Game.Levels.Union.L05union_comm

open Set

namespace STG4

variable {U : Type}

World "Union"
Level 6
Title "Union is associative"

Introduction
"
Here's an idea that you may find helpful for this proof:
If you're proving an \"or\" statement and you think you'll be
able to prove either the left or right side of the statement, then `apply Or.inl` or
`apply Or.inr` will set the goal to be the left or right side.  Alternatively, the tactic
`left` has the same effect as `apply Or.inl`, and `right` has the same effect as
`apply Or.inr`.

You can start this proof with either `ext x` or `apply Subset.antisymm`.
"

TheoremTab "∩∪"

/-- For any sets `A`, `B`, and `C`, `union_assoc A B C` is a proof of the
statement `(A ∪ B) ∪ C = A ∪ (B ∪ C)`.  In Mathlib, the name of this theorem is `Set.union_assoc`. -/
TheoremDoc STG4.union_assoc as "union_assoc" in "∩∪"

/-- For any sets $A$, $B$, and $C$, $(A \cup B) \cup C = A \cup (B \cup C)$. -/
Statement union_assoc (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  Hint "Notice that, as with intersections, Lean groups unions to the left, so
  `A ∪ B ∪ C` means `(A ∪ B) ∪ C`."
  apply Subset.antisymm
  intro x h
  rewrite [mem_union]
  rewrite [mem_union] at h
  cases' h with hAB hC
  cases' hAB with hA hB
  exact Or.inl hA
  Hint "Do you know which half of the goal you're going to prove now?"
  apply Or.inr
  exact Or.inl hB
  apply Or.inr
  exact Or.inr hC
  intro x h
  cases' h with hA hBC
  apply Or.inl
  exact Or.inl hA
  cases' hBC with hB hC
  apply Or.inl
  exact Or.inr hB
  exact Or.inr hC

NewHiddenTactic left right

Conclusion
"
You've mastered reasoning about complements, intersections, and unions.  In the next world,
we'll start mixing them up!
"
