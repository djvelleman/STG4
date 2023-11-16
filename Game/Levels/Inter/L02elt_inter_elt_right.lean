import Game.Levels.Inter.L01and

variable {U : Type}

World "Intersection"
Level 2
Title "Element of an intersection"

Introduction
"
In this level, we'll need to use the definition of \"intersection\".  The theorem that
expresses that definition is called `inter_def`.  If you have `x : U`, `A : Set U`, and
`B : Set U`, then `inter_def x A B` is a proof of the statement `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`.
As we saw in Complement World, that means that the tactic `rewrite [inter_def x A B]` can be
used to replace `x ∈ A ∩ B` in the goal with `x ∈ A ∧ x ∈ B`.  Usually Lean can figure out
`x`, `A`, and `B` on its own, so you can just write `rewrite [inter_def]`, and you can
use `rewrite [inter_def] at h` to do the replacement in an assumption `h` rather than
the goal.

Like `comp_def`, `inter_def` can be proven by using the `rfl` tactic.  But we
won't ask you to prove it; it is pre-defined in this game.  To enter the symbol `∩`, you
can type `\\inter` or `\\cap`.
"

DefinitionDoc inter as "∩"
"If `A` and `B` are sets, then `A ∩ B` is the intersection of `A` and `B`.
To enter the symbol `∩`, type `\\inter` or `\\cap`."

NewDefinition inter

LemmaTab "Set Theory"

LemmaDoc inter_def as "inter_def" in "Set Theory"
"If you have `x : U`, `A : Set U`, and `B : Set U`, then `inter_def x A B` is a proof of the
statement `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`."

lemma inter_def (x : U) (A B : Set U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by rfl

NewLemma inter_def

/-- Suppose $x \in A ∩ B$.  Then $x \in B$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  Hint "To start on this proof, try writing out the meaning of intersection in `h`."
  rewrite [inter_def] at h
  Hint "Now your situation is similar to the previous level."
  exact h.right

Conclusion
"
"
