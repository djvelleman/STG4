import Game.Levels.Combo.L04union_distrib_inter

variable {U : Type}

World "Combination"
Level 5
Title "A tricky subset proof"

Introduction
"
This proof is a bit tricky.  But you should know how to get started.
"

LemmaTab "Set Theory"

/-- Suppose $A \cup C \subseteq B \cup C$ and $A \cap C \subseteq B \cap C$.  Then $A \subseteq B$. -/
Statement (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x h3
  Hint (strict := true) "Now use `have` to assert that `{x} ∈ A ∪ C`.  Remember that, as
  explained in the description of the `have` tactic, you can do this even if you don't see
  how to justify the assertion in one step."
  have h4 : x ∈ A ∪ C
  rewrite [union_def]
  exact Or.inl h3
  Hint (strict := true) (hidden := true) "Use `h1`."
  have h5 : x ∈ B ∪ C := h1 h4
  Hint (strict := true) (hidden := true) "Now that you know `x ∈ B ∪ C`, you can use that
  statement as the basis for breaking your proof into cases."
  rewrite [union_def] at h5
  cases' h5 with h5B h5C
  exact h5B
  Hint (strict := true) (hidden := true) "Notice that you haven't used `h2` yet..."
  have h6 : x ∈ A ∩ C
  rewrite [inter_def]
  exact And.intro h3 h5C
  have h7 : x ∈ B ∩ C := h2 h6
  rewrite [inter_def] at h7
  exact h7.left

Conclusion
"
You've finished Combination World!
"
