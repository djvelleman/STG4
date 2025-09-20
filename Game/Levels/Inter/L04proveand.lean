import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Intersection"
Level 4
Title "Proving a conjunction"

Introduction
"
In this level we'll prove a statement of the form `P ∧ Q`.  To do this, we'll need
another theorem: `And.intro`.  If you have `h1 : P` and `h2 : Q`, then
`And.intro h1 h2` is a proof of `P ∧ Q`.
"

TheoremTab "Logic"

/-- If you have `h1 : P` and `h2 : Q`, then `And.intro h1 h2` is a proof of `P ∧ Q`. -/
TheoremDoc And.intro as "And.intro" in "Logic"

NewTheorem And.intro

/-- Suppose $x \in A$ and $x \in B$.  Then $x \in A \cap B$. -/
Statement (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  Hint "Writing out the meaning of intersection in the goal will help you see what to do to
  complete this level."
  rewrite [mem_inter_iff]
  Hint "Now you can use `And.intro` to prove the goal."
  Hint (hidden := true) "`exact And.intro h1 h2` will close the goal."
  exact And.intro h1 h2

Conclusion
"
Once again, the use of `rewrite` was not really necessary.  You could prove this
theorem with the single step `exact And.intro h1 h2`.
"
