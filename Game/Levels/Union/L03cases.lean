import Game.Levels.Union.L02subunion

variable {U : Type}

World "Union"
Level 3
Title "Proof by cases"

Introduction
"
In this proof, we'll need a new proof technique: proof by cases.  And we'll need a new
tactic to implement that technique in Lean: `cases'`.
"

TacticDoc cases'
"In this game, there are two situations in which we will use the `cases'` tactic.
* If you have an assumption `h : P ∨ Q`, then the tactic `cases' h with h1 h2` will break
your proof into cases.  In case 1, you'll have the new assumption `h1 : P`, and in case
2 you'll have `h2 : Q`.  In both cases you have to prove the original goal.
* If you have an assumption `h : ∃ x, P x`, then the tactic `cases' h with w hw` will
introduce a new object `w` and a new assumption `hw : P w` into the proof.
"

NewTactic cases'

/-- Suppose $A \subseteq C$ and $B \subseteq C$.  Then $A \cup B \subseteq C$. -/
Statement (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  Hint "Of course, to start a subset proof you need to introduce an object `x` and an
  assumption `h3`."
  intro x h3
  Hint "To understand the logic of this proof, it will help to write out the definition
  of union in {h3}."
  rewrite [union_def] at h3
  Hint "Now the assumption {h3} is an \"or\" statement.  The easiest way to use such an
  assumption is to break your proof into cases.  To do this in lean, use the tactic
  `cases' {h3} with {h3}A {h3}B`."
  cases' h3 with h3A h3B
  Hint "Now you have *two* goals.  For the first, the assumption `{x} ∈ A ∨ {x} ∈ B` has been
  replaced with `{x} ∈ A`, and for the second it has been replaced with `{x} ∈ B`.  In both
  cases, you must prove `{x} ∈ C`.  The two identifiers after `with` in the `cases'` tactic
  are used as the identifiers of the new assumptions in the two cases."
  exact h1 h3A
  exact h2 h3B

Conclusion
"
Note that Lean also has a `cases` tactic, but the syntax is a little more complicated.
That's why we have chosen to use the `cases'` tactic.
"
