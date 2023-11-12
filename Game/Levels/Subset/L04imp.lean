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
* If you are proving a statement of the form `∀ x, ...` then you can use
the tactic `intro x` to introduce a new object `x` into the proof.  Be sure to
use a variable name that is not already in use.

You can do multiple introductions in one step: for example, `intro x h` has the same
effect as doing `intro x` followed by `intro h`.
"

NewTactic intro

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

Conclusion
"
As usual, for more information about the new tactic `intro`, you can click on `intro`
in the list of tactics on the right.
"
