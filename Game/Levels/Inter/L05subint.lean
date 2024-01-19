import Game.Levels.Inter.L04proveand

variable {U : Type}

World "Intersection"
Level 5
Title "Subset of an intersection"

Introduction
"
Of course, you know by now how to start a proof that one set is a subset of another.
"

/-- Suppose $A \subseteq B$ and $A \subseteq C$.  Then $A \subseteq B \cap C$. -/
Statement (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x h3
  Hint "Writing out the definition of intersection in the goal will help."
  rewrite [inter_def]
  Hint "If you had `hB : {x} ∈ B` and `hC : {x} ∈ C`, then `And.intro hB hC`
  would prove the goal.  So there are two ways to proceed.  One possibility is to use
  `have` to introduce the assumptions `{x} ∈ B` and `{x} ∈ C`--that is, if you can see
  how to justify those statements!  Then you can use `And.intro` to prove the goal.

  The second possibility is to use the `apply` tactic.  Recall that if you write
  `apply And.intro`, then Lean will figure out that the
  theorem `And.intro` could be applied to prove the goal, if only you had proofs of
  `{x} ∈ B` and `{x} ∈ C`.  So it will set those two statements as goals, to be proven
  one after the other."
  apply And.intro
  Hint "Your immediate goal now is to prove that `{x} ∈ B`.  Once you close that goal,
  you'll be asked to prove the second goal, `{x} ∈ C`."
  exact h1 h3
  exact h2 h3

Conclusion
"
In general, if you think that some theorem `t` could be used to prove the goal, the tactic
`apply t` will work backwards from the goal, setting as new goals any hypotheses that are
needed for the application of the theorem `t`.

If your goal has the form `P ∧ Q`, then the `constructor` tactic will have the same
effect as `apply And.intro`; that is, it will set `P` and `Q` as goals to be proven.
"
