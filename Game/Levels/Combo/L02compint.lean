import Game.Levels.Combo.L01compunion

variable {U : Type}

World "Combination"
Level 2
Title "Complement of an intersection"

Introduction
"
Of course, you could start the proof in this level with either `ext x` or `apply sub_antisymm`.
But there is a shorter solution: you can use
the theorem from the previous level (`comp_union`) to prove the
theorem in this level.

The trick to get started on this proof is to rewrite `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`.  As you
know, `comp_comp (Aᶜ ∪ Bᶜ)` is a proof of the theorem `(Aᶜ ∪ Bᶜ)ᶜᶜ = Aᶜ ∪ Bᶜ`, and therefore
`rewrite [comp_comp (Aᶜ ∪ Bᶜ)]` could be used to rewrite `(Aᶜ ∪ Bᶜ)ᶜᶜ` as `Aᶜ ∪ Bᶜ`; but we
want to go in the opposite direction, rewriting `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`. To do that, use
`rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]`. (To enter the left-pointing arrow, type `\\l`.)
"

TheoremTab "ᶜ"

/-- For any sets `A` and `B`, `comp_inter A B` is a proof of the
statement `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`. -/
TheoremDoc comp_inter as "comp_inter" in "ᶜ"

/-- For any sets $A$ and $B$, $(A \cap B)^c = A^c \cup B^c$. -/
Statement comp_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]
  Hint "Do you see how you can now use the theorem from the previous level?"
  rewrite [comp_union]
  rewrite [comp_comp, comp_comp]
  rfl
