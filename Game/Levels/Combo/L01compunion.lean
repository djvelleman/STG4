import Game.Levels.Union

variable {U : Type}

World "Combination"
Level 1
Title "Complement of a union"

Introduction
"
As the proofs get harder, you may sometimes find that you want to use the `have` tactic
to assert a statement whose proof is too hard to do in a single line.  For an explanation
of how to do that, click on `have` in the list of tactics on the right.
"

LemmaTab "ᶜ"

LemmaDoc comp_union as "comp_union" in "ᶜ"
"For any sets `A` and `B`, `comp_union A B` is a proof of the
statement `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`."

/-- For any sets $A$ and $B$, $(A \cup B)^c = A^c \cap B^c$. -/
Statement comp_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [comp_def] at h1
  rewrite [inter_def, comp_def, comp_def]
  apply And.intro
  by_contra h2
  Hint (hidden := true) "To get a contradiction, prove `{x} ∈ A ∪ B`."
  apply h1
  exact Or.inl h2
  by_contra h2
  apply h1
  exact Or.inr h2
  intro h1
  rewrite [inter_def, comp_def, comp_def] at h1
  rewrite [comp_def]
  by_contra h2
  cases' h2 with h2A h2B
  exact h1.left h2A
  exact h1.right h2B

NewLemma comp_union

Conclusion
"

"
