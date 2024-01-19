import Game.Levels.Union.L04union_sub_swap

variable {U : Type}

World "Union"
Level 5
Title "Union is commutative"

Introduction
"
If you start your proof with `apply sub_antisymm`, then you'll be able to use
the theorem `union_sub_swap` that you proved in the last level.
"

TheoremTab "∩∪"

/-- For any sets `A` and `B`, `union_comm A B` is a proof of the
statement `A ∪ B = B ∪ A`. -/
TheoremDoc union_comm as "union_comm" in "∩∪"

/-- For any sets $A$ and $B$, $A \cup B = B \cup A$. -/
Statement union_comm (A B : Set U) : A ∪ B = B ∪ A := by
  apply sub_antisymm
  exact union_sub_swap A B
  exact union_sub_swap B A

Conclusion
"
Next we'll prove the associative law for unions.
"
