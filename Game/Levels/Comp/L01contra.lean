import Game.Levels.Subset

variable {U : Type}

World "Complement"
Level 1
Title "Proof by contradiction"

Introduction
"
To work with complements, we'll need to understand negative statements--that is, statements
that say that something is *not* the case.

If `P` is a statement, then `¬P` means \"it is not the case that P\".  To enter the symbol
`¬`, type `\\not`.

A common method of proving a negative statement is *proof by
contradiction*: to prove a statement of the form `¬P`, you can assume that `P` is true
and then show that this assumption leads to a contradiction.  The tactic to use for this
kind of proof is `by_contra`.
"

TacticDoc by_contra
"
If your goal is `¬P`, for some statement `P`, then the tactic
`by_contra h` will introduce the new assumption `h : P`, and set the
goal to be `False`.  If your goal is a statement `P` that is not a negative
statement, then `by_contra h` will introduce the new assumption
`¬P`.

To achieve your new goal, you will need to establish
`h1 : Q` and `h2 : ¬Q`, for some statement `Q`.  If you can do that,
then `h2 h1` will prove the goal `False`.  Notice that `h1 h2` will not be
recognized as a proof of `False`; the negative statement must come first.
"

NewTactic by_contra

DefinitionDoc not as "¬"
"`¬P` means \"it is not the case that P\".  To enter the symbol `¬`,
type `\\not`."

NewDefinition not

/-- Suppose $x \in A$ and $x \notin B$.  Then $\neg A \subseteq B$. -/
Statement {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  Hint "For the theorem in this level, your goal is `¬A ⊆ B`.  To use proof by contradiction
  in this proof, you must begin by introducing the assumption `h3 : A ⊆ B`.  To do that, type
  `by_contra h3`"
  by_contra h3
  Hint (strict := true) "Notice that the goal is now `False`.  To achieve that goal,
  you must prove contradictory statements.  You can do that by
  using `have` to assert `x ∈ B`, which will contradict `h2 : x ∉ B`."
  Hint (strict := true) (hidden := true) "`{h3} h1` is a proof of `x ∈ B`."
  have h4 : x ∈ B := h3 h1
  Hint (strict := true) "You can think of `h2 : x ∉ B` (which is shorthand for `h2 : ¬x ∈ B`)
  as meaning \"if `x ∈ B` were true, then that would lead to a contradiction\"--in other
  words, `x ∈ B → False`.
  Applying this to your new assumption `{h4} : x ∈ B` will give the contradiction
  you need.  In other words, `exact h2 {h4}` will close the goal."
  exact h2 h4

Conclusion
"
You can use the `by_contra` tactic in any proof to assume the
opposite of your goal.  But it is most useful when the goal
starts with the symbol `¬`.  After using the `by_contra` tactic,
you goal will be `False`.

To complete a proof by contradiction, you must prove contradictory statements.
If your goal is `False` and you have assumptions `h1 : P` and `h2 : ¬P`, for
some statement `P`, then `exact h2 h1` will close the goal.  Note that `exact h1 h2` won't
work; you must list the negative statement first to establish a contradiction.
"
