import Game.Levels.Subset.L02subhyp

variable {U : Type}

World "Subset"
Level 3
Title "The have tactic"

Introduction
"
In this level, we have hypotheses `h1 : A ⊆ B`, `h2 : B ⊆ C`, and `h3 : x ∈ A`.
As we saw in the last level, `h1 h3` is a proof that `x ∈ B`.  Unfortunately,
that is not the goal, so we can't use `exact h1 h3` to close the goal.
However, we can use the proof `h1 h3` to justify adding `h4 : x ∈ B` to our
list of assumptions.  To do that, we'll use a new tactic: `have`.
"

TacticDoc «have»
"
Use `have` to assert a statement that you can prove from your current
assumptions.  You must give the new assertion an identifier; be sure to
use an identifier that is different from those already in use.

If some expression `t` is a proof of a statement `P`, and `h` is an
identifier that is not in use, then `have h : P := t` will add `h : P`
to the list of assumptions.

Sometimes you want to assert a statement `P`, but the proof of `P` is too
difficult to be given in one line.  In that situation, you can simply write
`have h : P`.  Of course, you must still justify the assertion of `P`, so
the proof of `P` becomes your immediate goal.
Once the goal of proving `P` has been closed, you will be able to return to
your original goal, with `h : P` added to the assumption list.
"

NewTactic «have»

/-- Suppose $A \subseteq B$, $B \subseteq C$, and $x \in A$.  Then $x \in C$. -/
Statement (x : U) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  Hint "To get started on this proof, type `have h4 : x ∈ B := h1 h3`
  in the text box and click \"Execute\" or hit \"Return\" or \"Enter\".
  Recall that you can enter the symbol `∈` by typing `\\in`."
  have h4 : x ∈ B := h1 h3
  Hint "Notice that `{h4} : x ∈ B` has been added to the list of assumptions.
  Can you complete the proof now?"
  Hint (hidden := true) "As we saw in the last level, `h2 {h4}` is now
  a proof of the goal, so `exact h2 {h4}` will close the goal."
  exact h2 h4

Conclusion
"
You can use the `have` tactic to add a new statement to your list of
assumptions, as long as you can justify it with a proof.  For further
information, click on `have` in the list of tactics on the right.
"
