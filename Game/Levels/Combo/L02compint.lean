import Game.Metadata
import Game.Levels.Comp
import Game.Levels.Combo.L01compunion

open Set

namespace STG4

variable {U : Type}

World "Combination"
Level 2
Title "Complement of an intersection"

Introduction
"
Of course, you could start the proof in this level with either `ext x` or `apply Subset.antisymm`.
But there is a shorter solution: you can use
the theorem from the previous level (`compl_union`) to prove the
theorem in this level.

The trick to get started on this proof is to rewrite `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`.  As you
know, `compl_compl (Aᶜ ∪ Bᶜ)` is a proof of the theorem `(Aᶜ ∪ Bᶜ)ᶜᶜ = Aᶜ ∪ Bᶜ`, and therefore
`rewrite [compl_compl (Aᶜ ∪ Bᶜ)]` could be used to rewrite `(Aᶜ ∪ Bᶜ)ᶜᶜ` as `Aᶜ ∪ Bᶜ`; but we
want to go in the opposite direction, rewriting `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`. To do that, use
`rewrite [← compl_compl (Aᶜ ∪ Bᶜ)]`. (To enter the left-pointing arrow, type `\\l`.)
"

TheoremTab "ᶜ"

/-- For any sets `A` and `B`, `compl_inter A B` is a proof of the
statement `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`.  In Mathlib, the name of this theorem is `Set.compl_inter`. -/
TheoremDoc STG4.compl_inter as "compl_inter" in "ᶜ"

/-- For any sets $A$ and $B$, $(A \cap B)^c = A^c \cup B^c$. -/
Statement compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rewrite [← compl_compl (Aᶜ ∪ Bᶜ)]
  Hint "Do you see how you can now use the theorem from the previous level?"
  rewrite [compl_union]
  rewrite [compl_compl, compl_compl]
  rfl
