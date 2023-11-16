import Game.Levels.Combo.L01compunion

variable {U : Type}

World "Combination"
Level 2
Title "Complement of an intersection"

Introduction
"
Of course, one way to start on the proof in this level is `apply sub_antisymm`.
But there is a shorter solution: you can use
the theorem from the previous level (`comp_union`) to prove the
theorem in this level.  For a hint on how to do that, click on \"Show more help!\".
If you use
"

LemmaTab "Set Theory"

LemmaDoc comp_inter as "comp_inter" in "Set Theory"
"For any sets `A` and `B`, `comp_inter A B` is a proof of the
statement `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`."

/-- For any sets $A$ and $B$, $(A \cap B)^c = A^c \cup B^c$. -/
Statement comp_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  Hint "Of course, one way to start is `apply sub_antisymm`.  But there is also a way
  to use the theorem from the previous level (`comp_union`) to prove the
  theorem in this level.  For a hint on how to do that, click on \"Show more help!\"."
  Hint (hidden := true) "Start by rewriting `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`."
  Branch
    apply sub_antisymm
    Hint "For this proof, you may want to use the `have` tactic to assert a statement
    whose proof is too hard to do in a single line.  For an explanation of how to do that,
    click on `have` in the list of tactics on the right."
    intro x h1
    rewrite [union_def, comp_def, comp_def]
    rewrite [comp_def, inter_def] at h1
    by_contra h2
    have h3 : x ∈ A
    by_contra h3
    have h4 : x ∉ A ∨ x ∉ B := Or.inl h3
    exact h2 h4
    have h4 : x ∈ B
    by_contra h4
    have h5 : x ∉ A ∨ x ∉ B := Or.inr h4
    exact h2 h5
    have h5 : x ∈ A ∧ x ∈ B := And.intro h3 h4
    exact h1 h5
    intro x h1
    rewrite [comp_def, inter_def]
    rewrite [union_def, comp_def, comp_def] at h1
    by_contra h2
    cases' h1 with h1A h1B
    exact h1A h2.left
    exact h1B h2.right
  rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]
  rewrite [comp_union]
  rewrite [comp_comp, comp_comp]
  rfl

NewLemma comp_inter

Conclusion
"

"
