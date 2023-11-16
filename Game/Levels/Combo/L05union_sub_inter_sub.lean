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
  Hint (strict := true) "Now use `have` to assert that `{x} ∈ A ∪ C`.  If you don't see how to
  prove this statement in one step, you can leave off the `:=` part of the `have` tactic.  In
  other words, just write something like `have h4 : {x} ∈ A ∪ C`.  Then your immediate goal will
  be to prove that `{x} ∈ A ∪ C`.  Once you close that goal, you can return to the goal
  of proving `{x} ∈ B`, with `h4 : {x} ∈ A ∪ C` as an additional assumption."
  have h4 : x ∈ A ∪ C
  rewrite [union_def]
  exact Or.inl h3
  Hint (strict := true) "Now what inference can you make?"
  Hint (strict := true) (hidden := true) "Use `h1`."
  have h5 : x ∈ B ∪ C := h1 h4
  Hint (strict := true) (hidden := true) "Now that you know `x ∈ B ∪ C`, you can use that statement
  as the basis for breaking your proof into cases."
  rewrite [union_def] at h5
  cases' h5 with h5B h5C
  exact h5B
  Hint (strict := true) "Notice that you haven't used `h2` yet..."
  Hint (strict := true) (hidden := true) "You should be able to prove `x ∈ A ∩ C`.  Then
  you'll be able to use `h2`."
  have h6 : x ∈ A ∩ C
  rewrite [inter_def]
  exact And.intro h3 h5C
  have h7 : x ∈ B ∩ C := h2 h6
  rewrite [inter_def] at h7
  exact h7.left

Conclusion
"
You've finished Union World!
"
