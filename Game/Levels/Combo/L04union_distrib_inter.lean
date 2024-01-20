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
  Hint "You might be tempted to use `rewrite [comp_inter]` as your next step.  But
  in this situation, `rewrite [comp_inter]` is ambiguous, because there are
  two ways that the theorem `comp_inter` could be applied to rewrite the goal: `comp_inter B C`
  is a proof of `(B ∩ C)ᶜ = Bᶜ ∪ Cᶜ` and `comp_inter Aᶜ (B ∩ C)ᶜ` is a proof of
  `(Aᶜ ∩ (B ∩ C)ᶜ)ᶜ = Aᶝᶜ ∪ (B ∩ C)ᶜᶜ`, and either one of those equations could be used to
  rewrite the goal.  If you say `rewrite [comp_inter]`, then Lean will pick one of those two
  rewriting steps, and it might not pick the one you wanted.  So you'd better say explicitly
  what you want Lean to apply the theorem `comp_inter` to."
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
