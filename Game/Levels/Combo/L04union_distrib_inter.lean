import Game.Levels.Combo.L03inter_distrib_union

variable {U : Type}

World "Combination"
Level 4
Title "Union distributes over intersection"

Introduction
"
This is different from the previous theorem--the roles of union and intersection have
been swapped.

Once again, there is a tricky shortcut: there is a way to use the theorem from the
previous level to prove this theorem.

But if you don't see the shortcut, you can use a straightforward approach.
If you made it through the last one, you can do this one too!
"

TheoremTab "∩∪"

/-- For any sets `A`, `B`, and `C`, `union_distrib_over_inter A B C` is a proof of the
statement `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`. -/
TheoremDoc union_distrib_over_inter as "union_distrib_over_inter" in "∩∪"

/-- For any sets $A$, $B$, and $C$, $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$. -/
Statement union_distrib_over_inter (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rewrite [← comp_comp (A ∪ (B ∩ C))]
  rewrite [comp_union]
  rewrite [comp_inter B C]
  rewrite [inter_distrib_over_union]
  rewrite [comp_union]
  rewrite [comp_inter, comp_inter]
  rewrite [comp_comp, comp_comp, comp_comp]
  rfl

Conclusion
"
To finish off Union World, we'll do one more tricky theorem.
"
