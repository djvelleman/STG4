import Game.Levels.Subset.L05subref

variable {U : Type}

World "Subset"
Level 6
Title "Subset is transitive"

Introduction
"
To start a proof, you should look first at the goal.
What needs to be done to prove the goal?
In this level, the goal is `A ⊆ C`.  What does that
tell you about how to proceed?
"

LemmaTab "⊆"

LemmaDoc sub_trans as "sub_trans" in "⊆"
"
If you have `h1 : A ⊆ B` and `h2 : B ⊆ C`, then `sub_trans h1 h2` is a proof of `A ⊆ C`.
"

/-- Suppose $A \subseteq B$ and $B \subseteq C$.  Then $A \subseteq C$. -/
Statement sub_trans {A B C : Set U}
    (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  Hint (hidden := true) "To get started, you'll need to introduce first
  an object `x` and then the assumption that `x ∈ A`."
  intro x h3
  Hint "Does your situation now remind you of a previous level?"
  Hint (hidden := true) "First use `have` to assert that `{x} ∈ B`, and
  then prove `{x} ∈ C`."
  have h4 : x ∈ B := h1 h3
  exact h2 h4

NewLemma sub_trans

Conclusion
"
The theorem you have proven in this level shows that the subset relation has
a property called *transitivity*.  We have given the theorem the name `sub_trans`.
"
