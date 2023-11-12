import Game.Levels.Union.L01or

variable {U : Type}

World "Union"
Level 2
Title "Subset of a union"

Introduction
"
As with complements and intersections, one of the key tools for proving theorems about unions
is a theorem stating the definition.  If you have `x : U`, `A : Set U`, and `B : Set U`,
then `union_def x A B` is a proof of the statement `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`.
That means you can use `rewrite [union_def]` to write out the definition of
`x ∈ A ∪ B` if it appears in any assumption or the goal.
"

DefinitionDoc union as "∪"
"If `A` and `B` are sets, then `A ∪ B` is the unlon of `A` and `B`.
To enter the symbol `∪`, type `\\union`."

NewDefinition union

LemmaTab "Set Theory"

LemmaDoc union_def as "union_def" in "Set Theory"
"If you have `x : U`, `A : Set U`, and `B : Set U`, then `union_def x A B` is a proof of the
statement `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`."

lemma union_def (x : U) (A B : Set U) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by rfl

NewLemma union_def

/-- Suppose $A$ and $B$ are sets.  Then $B \subseteq A \cup B$. -/
Statement (A B : Set U) : B ⊆ A ∪ B := by
  Hint (hidden := true) "Your goal is a subset statement.
  That should tell you how to get started."
  intro x h
  Hint "Writing out the definition of union in the goal should help you see how to proceed."
  rewrite [union_def]
  exact Or.inr h

Conclusion
"
Next, we'll see how to prove that a union is a subset of another set.
"
