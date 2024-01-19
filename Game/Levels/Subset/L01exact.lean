import Game.Metadata

variable {U : Type}

World "Subset"
Level 1
Title "The exact tactic"

Introduction
"
# Read this first

Each level in this game involves proving a mathematical statement (the \"Goal\").
When you give a proof of this statement that
is accepted by Lean, we say that you have *closed* the goal.

In this first level you're going to prove that if `x` belongs to the universe `U`,
`A` is a set of objects from `U`, and `x ∈ A`, then `x ∈ A`.  You should see
`U : Type`, `x : U`, and `A : Set U` under *Objects* in the pane to the right, and
`h : x ∈ A` under *Assumptions*.  The letter `h` here is called an *identifier*
for the assumption `x ∈ A`.

You will prove goals in Lean using *tactics*.  The first tactic you're
going to learn is called `exact`, and it is used to close the goal.
You can close the goal by typing `exact` followed by a proof of the goal.
"

/-- Use `exact` to close a goal.  If some expression `t` is a proof of
the goal, then `exact t` will close the goal.

Think of "exact" as meaning "this is exactly what is needed to prove the goal." -/
TacticDoc exact

NewTactic exact

/-- `x ∈ A` means that `x` is an element of `A`.  To enter the symbol `∈`, type
`\mem` or `\in`. -/
DefinitionDoc elt as "∈"

NewDefinition elt

/-- Let $x$ be an object in the universe $U$, and let $A$ be a set whose elements
come from $U$.  Suppose that $x ∈ A$.  Then $x \in A$. -/
Statement (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  Hint "In order to complete this proof, type `exact h` in the text box
  under the goal and click on \"Execute\" or hit the \"Return\" or \"Enter\" key."
  exact h

Conclusion
"
Congratulations! You have completed your first verified proof!

Although this theorem was trivial, it illustrates an important fact: although we
called `h` an *identifier* for the assumption `x ∈ A`, it is also recognized by Lean
as a *proof* of the statement `x ∈ A`.  Any time you see `h : P`
listed as an assumption, where `P` is some statement, that means that Lean will
recognize `h` as a proof of the statement `P`.

Remember that `exact` is a *tactic*. If you ever want information about the `exact` tactic,
you can click on `exact` in the list of tactics on the right.

Now click on \"Next\" to see a more interesting use of the `exact` tactic.
"
