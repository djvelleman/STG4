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
theorem in this level.  For a hint on how to do that, click on \"Show more help!\".
"

LemmaTab "ᶜ"

LemmaDoc comp_inter as "comp_inter" in "ᶜ"
"For any sets `A` and `B`, `comp_inter A B` is a proof of the
statement `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`."

/-- For any sets $A$ and $B$, $(A \cap B)^c = A^c \cup B^c$. -/
Statement comp_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  Hint (hidden := true) "Start by rewriting `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`."
  rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]
  rewrite [comp_union]
  rewrite [comp_comp, comp_comp]
  rfl

NewLemma comp_inter

Conclusion
"
"
