import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Combination"
Level 5
Title "A tricky subset proof"

Introduction
"
This proof is a bit tricky.  But you should know how to get started.
"

/-- Suppose $A \cup C \subseteq B \cup C$ and $A \cap C \subseteq B \cap C$.  Then $A \subseteq B$. -/
Statement (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x h3
  Hint (strict := true) "Now use `have` to assert that `{x} ∈ A ∪ C`.  If you don't see right
  away how to justify this assertion, you can just write `have hAC : {x} ∈ A ∪ C` and Lean will
  set `{x} ∈ A ∪ C` as your immediate goal.  Once you achieve that goal, Lean will add
  `hAC : {x} ∈ A ∪ C` to your list of assumptions, and you can continue with
  the proof of your original goal.  For further details, click on `have` in the list of tactics
  on the right."
  have h4 : x ∈ A ∪ C
  rewrite [mem_union]
  exact Or.inl h3
  Hint (strict := true) (hidden := true) "Use `h1`."
  have h5 : x ∈ B ∪ C := h1 h4
  Hint (strict := true) (hidden := true) "Now that you know `{x} ∈ B ∪ C`, you can use that
  statement as the basis for breaking your proof into cases."
  rewrite [mem_union] at h5
  rcases h5 with h5B | h5C
  exact h5B
  Hint (strict := true) (hidden := true) "Notice that you haven't used `h2` yet..."
  have h6 : x ∈ A ∩ C
  rewrite [mem_inter_iff]
  exact And.intro h3 h5C
  have h7 : x ∈ B ∩ C := h2 h6
  rewrite [mem_inter_iff] at h7
  exact h7.left

Conclusion
"
You've finished Combination World!
"
