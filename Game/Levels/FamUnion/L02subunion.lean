import Game.Levels.FamUnion.L01proveexists

open Set

namespace STG4

variable {U : Type}

World "FamUnion"
Level 2
Title "Subset of family union"

Introduction
"
In mathematical writing, the union of the family $F$ is usually denoted $\\bigcup F$.
In Lean, the union of a family `F` is denoted `⋃₀ F`.  (You can enter the symbol
`⋃₀` by typing `\\U0`.)

Suppose we have `F : Set (Set U)` and `x : U`.  Then `x ∈ ⋃₀ F` means that there is at least
one set `t` such that `t ∈ F` and `x ∈ t`.  To write this statement in Lean, we write
`∃ t, t ∈ F ∧ x ∈ t`.  Lean abbreviates this statement as `∃ t ∈ F, x ∈ t`.

As with other set theory operations, we have a theorem that expresses this definition.  Lean will
recognize `mem_sUnion` as a proof of any statement of the form `x ∈ ⋃₀ F ↔ ∃ t ∈ F, x ∈ t`.

In this level, you'll try out these ideas.
"

/-- `⋃₀ F` is the union of the family of sets `F`.  To enter the symbol `⋃₀`, type `\U0`. -/
DefinitionDoc famunion as "⋃₀"

NewDefinition famunion

/-- Lean will recognize `mem_sUnion` as a proof of any statement of the form
`x ∈ ⋃₀ F ↔ ∃ t ∈ F, x ∈ t`.  In Mathlib, the name of this theorem is `Set.mem_sUnion`. -/
TheoremDoc Set.mem_sUnion as "mem_sUnion" in "⋂₀⋃₀"

NewTheorem Set.mem_sUnion

TheoremTab "⋂₀⋃₀"

/-- If your goal is `∃ x, P x`, where `P x` represents some statement about `x`, and `a` is a
value that could be assigned to `x`, then the tactic `use a` will
set `P a` to be the goal.  It will then see if this new goal follows easily from your
assumptions, and if so it will close the goal. -/
TacticDoc use

NewTactic use

TheoremTab "⋂₀⋃₀"

/-- Suppose $F$ is a family of sets and $A \in F$.  Then $A \subseteq \bigcup F$. -/
Statement (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x h2
  rewrite [mem_sUnion]
  Hint "Remember that the goal `∃ t ∈ F, {x} ∈ t` is an abbreviation for
  `∃ t, t ∈ F ∧ {x} ∈ t`.  As we saw in the last level, we can prove this by coming up with
  a witness--that is, a value for `t` that will make the statement `t ∈ F ∧ {x} ∈ t` come out
  true.  Looking at
  `h1` and `{h2}`, it looks like `t = A` would work.  That suggests a way to proceed:
  `Exists.intro A hA` would prove the goal, if `hA` were a proof of `A ∈ F ∧ {x} ∈ A`.  In
  other words, if `Exists.intro A` is applied to a proof of `A ∈ F ∧ {x} ∈ A`, then it will
  prove the goal.  So if you use the tactic `apply Exists.intro A`, then Lean will
  set `A ∈ F ∧ {x} ∈ A` as your new goal."
  apply Exists.intro A
  exact And.intro h1 h2

Conclusion
"
There is another tactic you could have used to complete this proof.  Instead of
`apply Exists.intro A`, you could write `use A`.  The `use` tactic is actually a powerful
tactic.  Not only does it fill in `A` for `t` in the existential goal, it then tries to
complete the proof on its own--and in this case, it would have succeeded!
"
