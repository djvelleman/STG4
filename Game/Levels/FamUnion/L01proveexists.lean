import Game.Levels.FamInter

open Set

namespace STG4

variable {U : Type}

World "FamUnion"
Level 1
Title "Proving existential statements"

Introduction
"
To work with unions of families, we'll need to know how to work with existential statements.
If `P x` is a statement about an unspecified object `x`, then `∃ x, P x` means \"there is
at least one `x` such that `P x` is true\".  The symbol `∃` is called the *existential
quantifier*, and you can enter it in Lean by typing `\\exists`.

The easiest way to prove the statement `∃ x, P x` is to specify a value of `x`, and give a
proof of `P x` for that value of `x`.  The theorem that allows you to do that is called
`Exists.intro`.  If you have `h : P a`, for some object `a`, then `Exists.intro a h` is a
proof of the statement `∃ x, P x`.  (The object `a` is sometimes called a *witness* for
the existential statement.)  In this level, you'll try out this theorem.
"

/-- If `P x` represents a statement about `x`, then `∃ x, P x` means "there is at least one
`x` such that `P x` is true".  To enter the symbol `∃`, type `\exists`.

### If your goal is `∃ x, P x`

If you have `h : P a`, for some object `a`, then `Exists.intro a h` is a proof of `∃ x, P x`,
so `exact Exists.intro a h` will close the goal.
If you think `P a` is true, but you don't yet have a proof of it, then `apply Exists.intro a`
will set `P a` as your goal.  The tactic `use a` does the same thing, but it also tries to
prove `P a`; if it doesn't succeed, then it leaves `P a` as a goal for you to prove.

### If you have an assumption `h : ∃ x, P x`

The tactic `obtain ⟨w, hw⟩ := h` will
introduce a new object `w` and a new assumption `hw : P w` into the proof.  To enter the
angle brackets `⟨ ⟩`, type either `\<` and `\>` or `\langle` and `\rangle`.
-/
DefinitionDoc ex as "∃"

NewDefinition ex

/-- If `P x` represents a statement about `x` and you have `h : P a`, for some object `a`, then
`Exists.intro a h` is a proof of `∃ x, P x`. -/
TheoremDoc Exists.intro as "Exists.intro" in "Logic"

NewTheorem Exists.intro

/--Suppose $A$ is a set.  Then there is some set $S$ such that $S \subseteq A$.-/
Statement (A : Set U) : ∃ s, s ⊆ A := by
  Hint (strict := true) "Your goal says that there is a set that is a subset of `A`.
  The theorem `Subset.refl` suggests such a set."
  Hint (strict := true) (hidden := true) "Recall that `Subset.refl A` is a proof of `A ⊆ A`.
  So start your proof with `have h : A ⊆ A := Subset.refl A`."
  Branch
    use ∅
    Hint "Although `∅` is a reasonable choice for a set that is a subset of `A`, it is difficult
    to complete the proof with this choice using only methods developed so far in this game.
    Go back and try a different choice."
  have h : A ⊆ A := Subset.refl A
  Hint "Now you can use `Exists.intro` to complete the proof."
  Hint (hidden := true) "`Exists.intro A {h}` is a proof of the goal, so `exact Exists.intro A {h}`
  will close the goal."
  exact Exists.intro A h

Conclusion
"
By the way, another set that would have worked as a witness for the existential goal in this
theorem is the empty set, denoted `∅`.  However, to justify the use of that witness you would
have had to prove `∅ ⊆ A`.  Since we already have the theorem `Subset.refl`, it was easier to use
`A` as the witness.

Now that you know how to prove existential statements, you're ready to start working with
unions of families.
"
