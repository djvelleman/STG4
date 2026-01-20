import Game.Levels.Inter

open Set

namespace STG4

variable {U : Type}

World "Union"
Level 1
Title "Or"

Introduction
"
For working with unions, the important logical word is \"or\".

If `P` and `Q` are statements, then `P ∨ Q` means \"`P` or `Q` or both\".  To enter the
symbol `∨`, type `\\or`.  For the statement `P ∨ Q` to be true, either `P` or `Q` must
be true.  This gives us two ways to prove a statement of this form.  If you have
`h : P`, then `Or.inl h` can be used to prove `P ∨ Q`.  If you have `h : Q`, then
`Or.inr h` proves `P ∨ Q`.
"

/-- `P ∨ Q` means "`P` or `Q` or both".  To enter the symbol `∨`, type `\or`.

### If your goal is `P ∨ Q`

If you have `hP : P`, then `Or.inl hP` is a proof of `P ∨ Q`, so `exact Or.inl hP`
will close the goal.  Similarly, if you have `hQ : Q`, then `Or.inr hQ` is a proof
of `P ∨ Q`.  If you don't have a proof of either `P` or `Q`, but you think you know
which one is true, then you can use `apply Or.inl` to set the goal to be `P`, or
`apply Or.inr` to set the goal to be `Q`.  Alternatively, the tactic `left` will have
the same effect as `apply Or.inl`, and `right` will have the same effect as
`apply Or.inr`.

### If you have an assumption `h : P ∨ Q`

A good strategy would be to use proof by cases.  The tactic `rcases h with hP | hQ`
will break the proof into two cases.  In case 1, the assumption `h` is replaced by
`hP : P `, and in case 2 it is replaced by `hQ : Q`.  In both cases, you must prove
the goal.
-/
DefinitionDoc or as "∨"

NewDefinition or

TheoremTab "Logic"

/-- If you have `h : P`, then `Or.inl h` can be used as a proof of `P ∨ Q`, for
any statement `Q`. -/
TheoremDoc Or.inl as "Or.inl" in "Logic"

/-- If you have `h : Q`, then `Or.inr h` can be used as a proof of `P ∨ Q`, for
any statement `P`. -/
TheoremDoc Or.inr as "Or.inr" in "Logic"

NewTheorem Or.inl Or.inr

/-- Suppose $x \in A$, and $B$ is any set.  Then $x \in A ∨ x ∈ B$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  Hint (hidden := true) "`Or.inl h` is a proof of the goal."
  exact Or.inl h

Conclusion
"
Now we're ready to start proving theorems about unions.
"
