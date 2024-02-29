import Game.Levels.Combo.L03inter_distrib_union

open Set

namespace STG4

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

/-- For any sets `A`, `B`, and `C`, `union_distrib_left A B C` is a proof of the
statement `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`.  In Mathlib, the name of this theorem
is `Set.union_distrib_left`. -/
TheoremDoc STG4.union_distrib_left as "union_distrib_left" in "∩∪"

/-- For any sets $A$, $B$, and $C$, $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$. -/
Statement union_distrib_left (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rewrite [← compl_compl (A ∪ (B ∩ C))]
  rewrite [compl_union]
  Hint "You might be tempted to use `rewrite [compl_inter]` as your next step.  But
  in this situation, `rewrite [compl_inter]` is ambiguous, because there are
  two ways that the theorem `compl_inter` could be applied to rewrite the goal: `compl_inter B C`
  is a proof of `(B ∩ C)ᶜ = Bᶜ ∪ Cᶜ` and `compl_inter Aᶜ (B ∩ C)ᶜ` is a proof of
  `(Aᶜ ∩ (B ∩ C)ᶜ)ᶜ = Aᶝᶜ ∪ (B ∩ C)ᶜᶜ`, and either one of those equations could be used to
  rewrite the goal.  If you say `rewrite [compl_inter]`, then Lean will pick one of those two
  rewriting steps, and it might not pick the one you wanted.  So you'd better say explicitly
  what you want Lean to apply the theorem `compl_inter` to."
  rewrite [compl_inter B C]
  rewrite [inter_distrib_left]
  rewrite [compl_union]
  rewrite [compl_inter, compl_inter]
  rewrite [compl_compl, compl_compl, compl_compl]
  rfl

Conclusion
"
To finish off Combination World, we'll do one more tricky theorem.
"
