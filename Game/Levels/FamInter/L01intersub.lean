import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "FamInter"
Level 1
Title "Family intersection is subset"

Introduction
"
In mathematical writing, the intersection of the family $F$ is usually denoted $\\bigcap F$.
In Lean, the intersection of a family `F` is denoted `⋂₀ F`.  (You can enter the symbol
`⋂₀` by typing `\\I0`.)

Suppose we have `F : Set (Set U)` and `x : U`.  Then `x ∈ ⋂₀ F` means that for every set `t`, if
`t` is in `F`, then `x ∈ t`.  To write this statement in Lean, we write `∀ t, t ∈ F → x ∈ t`.
Lean abbreviates this statement as `∀ t ∈ F, x ∈ t`.
The symbol `∀` is called the *universal quantifier*, and you can enter it in Lean by typing
`\\forall`.  Note that `∀ t, t ∈ F → x ∈ t` means `∀ t, (t ∈ F → x ∈ t)`, not
`(∀ t, t ∈ F) → x ∈ t`.  In other words, Lean interprets the universal quantifier as applying
to the entire rest of the statement.  If you want it to apply to less, you have to
use parentheses to indicate that.

As with other set theory operations, we have a theorem that expresses this definition.  Lean will
recognize `mem_sInter` as a proof of any statement of the form `x ∈ ⋂₀ F ↔ ∀ t ∈ F, x ∈ t`.

In this level, you'll try out these ideas.
"

/-- `⋂₀ F` is the intersection of the family of sets `F`.  To enter the symbol `⋂₀`, type `\I0`. -/
DefinitionDoc famint as "⋂₀"

/-- If `P x` represents a statement about an unspecified object `x`, then `∀ x, P x` means
"for all `x`, `P x` is true".  To enter the symbol `∀`, type `\forall`.

### If your goal is `∀ x, P x`

The tactic `intro t` will introduce a new object `t` into the proof, and set the goal to be `P t`.
Be sure to use a variable `t` that is not already being used to stand for some object.

### If you have an assumption `h : ∀ x, P x`

If `a` stands for some object, then `h a` is a proof of `P a`.  Note that `a` must be the
right *type* of object.  For example, if `x` stands for an object in the universe `U`, then
`a` must have type `U`; if `x` stands for a set of objects from the universe `U`, then `a` must
have type `Set U`.
-/
DefinitionDoc all as "∀"

NewDefinition famint all

/-- Lean will recognize `mem_sInter` as a proof of any statement of the form
`x ∈ ⋂₀ F ↔ ∀ t ∈ F, x ∈ t`.  In Mathlib, the name of this theorem is `Set.mem_sInter`. -/
TheoremDoc Set.mem_sInter as "mem_sInter" in "⋂₀⋃₀"

NewTheorem Set.mem_sInter

TheoremTab "⋂₀⋃₀"

/-- Suppose $F$ is a family of sets and $A \in F$.  Then $\bigcap F \subseteq A$. -/
Statement (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x h2
  Hint "As usual, you may find it helpful to use the `rewrite` tactic to write out the
  definition of `{x} ∈ ⋂₀ F`, using the theorem `mem_sInter`."
  rewrite [mem_sInter] at h2
  Hint "Remember that `{h2} : ∀ t ∈ F, {x} ∈ t` is an abbreviation for
  `{h2} : ∀ t, t ∈ F → {x} ∈ t`.  Since `∀` means \"for all\", `{h2}` can be applied to any
  set--that is, we can plug in any set for `t` in `{h2}`.
  In particular, applying it to the set `A`, we can conclude that `A ∈ F → {x} ∈ A`.
  To apply `{h2}` to `A`, we just write `{h2}` followed by `A`, with a space between them.
  Thus, your next step can be `have {h2}A : A ∈ F → {x} ∈ A := {h2} A`.  You can save yourself
  a little typing by writing `have {h2}A := {h2} A`; Lean will figure out what statement is
  proven by `{h2} A`."
  have h2A : A ∈ F → x ∈ A := h2 A
  Hint "Since we also have `h1 : A ∈ F`, you can apply `{h2A}` to `h1` to prove that `{x} ∈ A`.
  This means that `{h2A} h1` is a proof of the goal."
  exact h2A h1

Conclusion
"
The last two steps could have been combined into one step.  In general, if you have
`h1 : A ∈ F` and `h2 : ∀ t ∈ F, P t`, where `P t` is some statement about `t`, then `h2 A`
is a proof of `A ∈ F → P A`, and
applying that proof to `h1` we conclude that `h2 A h1` is a proof of `P A`.  For example,
if you have `h1 : A ∈ F` and `h2 : ∀ t ∈ F, x ∈ t`, then `h2 A h1` is a proof of `x ∈ A`.
"
