import Game.Levels.FamInter

variable {U : Type}

World "FamUnion"
Level 1
Title "Proving existential statements"

Introduction
"
To work with unions of families, we'll need to know how to work with existential statements.
If `P x` is a statement about an unspecified object `x`, then `∃ x, P x` means \"there is
at least one `x` such that `P x` is true\".  The symbol `∃` is called the
*existential quantifier*, and you can enter it in Lean by typing `\\exists`.

The easiest way to prove the statement `∃ x, P x` is to specify a value of `x`, and give a
proof of `P x` for that value of `x`.  The theorem that allows you to do that is called
`Exists.intro`.  If you have `h : P a`, for some object `a`, then `Exists.intro a h` is a
proof of the statement `∃ x, P x`.  In this level, you'll try out this theorem.
"

DefinitionDoc ex as "∃"
"If `P x` represents a statement about `x`, then `∃ x, P x` means \"there is at least one
`x` such that `P x` is true\".  To enter the symbol `∃`, type `\\exists`."

NewDefinition ex

LemmaDoc Exists.intro as "Exists.intro" in "Logic"
"If `P x` represents a statement about `x` and you have `h : P a`, for some object `a`, then
`Exists.intro a h` is a proof of `∃ x, P x`."

NewLemma Exists.intro

/--Suppose $A$ is a set.  Then there is some set $S$ such that $S \subseteq A$.-/
Statement (A : Set U) : ∃ S, S ⊆ A := by
  Hint (strict := true) "Your goal says that there is a set that is a subset of `A`.  Can you think of such a set?"
  Hint (strict := true) (hidden := true) "Recall that `sub_ref A` is a proof of `A ⊆ A`.  So start your proof
  with `have h : A ⊆ A := sub_ref A`."
  have h : A ⊆ A := sub_ref A
  Hint "Now you can use `Exists.intro` to complete the proof."
  Hint (hidden := true) "Exists.intro A {h}` proves the goal."
  exact Exists.intro A h

Conclusion
"
Now that you know how to prove existential statements, you're ready to start working with
unions of families.
"
