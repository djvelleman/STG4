import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Union"
Level 2
Title "Subset of a union"

Introduction
"
As with complements and intersections, one of the key tools for proving theorems about unions
is a theorem stating the definition.  If you have `x : U`, `A : Set U`, and `B : Set U`,
then `mem_union x A B` is a proof of the statement `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`.
That means you can use `rewrite [mem_union]` to write out the definition of
`x ∈ A ∪ B` if it appears in any assumption or the goal.  (The similar theorem about intersections
was called `mem_inter_iff`.  Why isn't this one called `mem_union_iff`?  I don't know.  The
naming of theorems in Lean is systematic, but there are occasional surprises.)
"

/-- If `A` and `B` are sets, then `A ∪ B` is the union of `A` and `B`.
To enter the symbol `∪`, type `\union`. -/
DefinitionDoc union as "∪"

NewDefinition union

TheoremTab "∩∪"

/-- If you have `x : U`, `A : Set U`, and `B : Set U`, then `mem_union x A B` is a proof of the
statement `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`.  In Mathlib, the name of this theorem is `Set.mem_union`. -/
TheoremDoc Set.mem_union as "mem_union" in "∩∪"

NewTheorem Set.mem_union

/-- Suppose $A$ and $B$ are sets.  Then $B \subseteq A \cup B$. -/
Statement (A B : Set U) : B ⊆ A ∪ B := by
  Hint (hidden := true) "Your goal is a subset statement.
  That should tell you how to get started."
  intro x h
  Hint "Writing out the definition of union in the goal should help you see how to proceed."
  rewrite [mem_union]
  exact Or.inr h

Conclusion
"
Next, we'll see how to prove that a union is a subset of another set.
"
