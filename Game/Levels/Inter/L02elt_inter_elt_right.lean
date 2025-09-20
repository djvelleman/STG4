import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Intersection"
Level 2
Title "Element of an intersection"

Introduction
"
In this level, we'll need to use the definition of \"intersection\".  The theorem that
expresses that definition is called `mem_inter_iff`.  If you have `x : U`, `A : Set U`, and
`B : Set U`, then `mem_inter_iff x A B` is a proof of the statement `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`.
As we saw in Complement World, that means that the tactic `rewrite [mem_inter_iff x A B]` can be
used to replace `x ∈ A ∩ B` in the goal with `x ∈ A ∧ x ∈ B`.  Usually Lean can figure out
`x`, `A`, and `B` on its own, so you can just write `rewrite [mem_inter_iff]`, and you can
use `rewrite [mem_inter_iff] at h` to do the replacement in an assumption `h` rather than
the goal.

Like `mem_compl_iff`, `mem_inter_iff` can be proven by using the `rfl` tactic.  But we
won't ask you to prove it; it is pre-defined in this game.  To enter the symbol `∩`, you
can type `\\inter` or `\\cap`.
"

/-- If `A` and `B` are sets, then `A ∩ B` is the intersection of `A` and `B`.
To enter the symbol `∩`, type `\inter` or `\cap`. -/
DefinitionDoc inter as "∩"

NewDefinition inter

TheoremTab "∩∪"

/-- If you have `x : U`, `A : Set U`, and `B : Set U`, then `mem_inter_iff x A B` is a proof of the
statement `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`.
In Mathlib, the name of this theorem is `Set.mem_inter_iff`. -/
TheoremDoc Set.mem_inter_iff as "mem_inter_iff" in "∩∪"

NewTheorem Set.mem_inter_iff

/-- Suppose $x \in A ∩ B$.  Then $x \in B$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  Hint "To start on this proof, try writing out the meaning of intersection in `h`."
  rewrite [mem_inter_iff] at h
  Hint "Now your situation is similar to the previous level."
  exact h.right
