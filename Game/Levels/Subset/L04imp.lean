import Game.Levels.Subset.L03have

variable {U : Type}

World "Subset"
Level 4
Title "Implication"

Introduction
"
If `P` and `Q` are statements, then `P → Q` means \"if P then Q\".
To enter the symbol `→`, type `\\imp` (short for \"implies\").

The most straightforward way to prove a statement of the form `P → Q` is to assume that
`P` is true and then prove `Q`.  To do that, we'll need a new tactic: `intro`.
"

DefinitionDoc imp as "→"
"`P → Q` means \"if `P` then `Q`\".  You can enter the symbol `→` by typing `\\imp`."

NewDefinition imp

TacticDoc intro
"
Use `intro` to introduce either a new assumption or a new object into your proof.

There are two situations in which you can use the `intro` tactic:
* If you are proving a statement of the form `P → Q`, then you can use
the tactic `intro h` to introduce the assumption `h : P` and set `Q` as the goal.  Be
sure to use an identifier that is not already in use.
* If you are proving a statement of the form `∀ x, P x`, where `P x` is some statement
about `x`, then you can use the tactic `intro x` to introduce a new object `x` into the proof.
Be sure to use a variable name that is not already in use.  The goal will then be `P x`.

You can do multiple introductions in one step: for example, `intro x h` has the same
effect as doing `intro x` followed by `intro h`.
"

NewTactic intro

/-- Let $x$ be an object from the universe $U$, and let $A$, $B$, and $C$ be sets
such that $A \subseteq B$ and $x \in B \to x \in C$.  Then $x \in A → x \in C$.-/
Statement {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  Hint "Since our goal in this level is the statement `x ∈ A → x ∈ C`, our first step for
  this proof is to assume `x ∈ A`.  To introduce that assumption,
  assigning it the identifier `h3`, type `intro h3`."
  intro h3
  Hint "Notice that `{h3} : x ∈ A` is now listed under *Assumptions*, and your new goal is
  `x ∈ C`."
  Hint (hidden := true) "As you saw in the previous level, you can now apply `h1` to `{h3}`
  to justify asserting `x ∈ B`, using the `have` tactic."
  have h4 : x ∈ B := h1 h3
  Hint (strict := true) "Just as you were able to apply `h1` to `{h3}` in the last step,
  you can now apply `h2` to `{h4}` to prove the goal."
  exact h2 h4

/-
/-- Suppose $A \subseteq B$ and $x$ is any object in the universe $U$.
Then $x \in A \to x \in B$. -/
Statement {A B : Set U} (h1 : A ⊆ B) (x : U) : x ∈ A → x ∈ B := by
  Hint "Since our goal in this level is the statement `x ∈ A → x ∈ B`, our first step for
  this proof is to assume `x ∈ A`.  To introduce that assumption,
  assigning it the identifier `h2`, type `intro h2`."
  intro h2
  Hint "Notice that `{h2} : x ∈ A` is now listed under *Assumptions*, and your new goal is
  `x ∈ B`."
  Hint (hidden := true) "h1 {h2} is now a proof of the goal."
  exact h1 h2
-/

Conclusion
"
In general, if your goal has the form `P → Q`, then the tactic `intro h` will add `h : P` to
the list of assumptions and set `Q` to be the goal.  If you have assumptions
`h1 : P → Q` and `h2 : P`, then `h1 h2` is a proof of `Q`.  This is another example of a proof
acting like a function: a proof of `P → Q` can be thought of as a function which, when
applied to a proof of `P`, produces a proof of `Q`.

As usual, for more information about the new tactic `intro`, you can click on `intro`
in the list of tactics on the right.
"
