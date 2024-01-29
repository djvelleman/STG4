import Game.Levels.Union

variable {U : Type}

World "Combination"
Level 1
Title "Complement of a union"

Introduction
"
There is more than one way to do the proof in this level.  Since the proof involves complements of
sets, negative statements will arise in the course of the proof.  This suggests two possible techniques.
You may be able to use the `push_neg` tactic to reexpress some negative statements as equivalent
positive statements.  And you may find proof by contradiction useful.
"

TheoremTab "ᶜ"

/-- For any sets `A` and `B`, `comp_union A B` is a proof of the
statement `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`. -/
TheoremDoc comp_union as "comp_union" in "ᶜ"

/-- For any sets $A$ and $B$, $(A \cup B)^c = A^c \cap B^c$. -/
Statement comp_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  rewrite [comp_def, union_def]
  push_neg
  rfl
