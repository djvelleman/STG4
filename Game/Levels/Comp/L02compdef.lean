import Game.Levels.Comp.L01contra

open Set

namespace STG4

variable {U : Type}

World "Complement"
Level 2
Title "Definition of complement"

Introduction
"
If you have `A : Set U`, then `Aᶜ` is defined to be the set of all objects in the universe `U`
that are not elements of `A`.  That means that if you also have `x : U`, then the statements
`x ∈ Aᶜ` and `x ∉ A` are equivalent.  We express this by saying that the statement
`x ∈ Aᶜ ↔ x ∉ A` is true.  (The symbol `↔` means \"if and only if\", and you can enter it
by typing `\\iff`.  You can enter the superscript `c` in the notation for the complement
of a set by typing `\\compl` or `\\^c`.)

In this level, we're going to prove that the statement `x ∈ Aᶜ ↔ x ∉ A` is true, and to do
it we'll use a new tactic: `rfl`.  The `rfl` tactic can prove any statement of the form
`P ↔ Q` if `P` and `Q` are statements that are equivalent by virtue of the definitions of
the symbols occurring in them.  (We say in this case that `P` and `Q` are *definitionally
equivalent*.)  The `rfl` tactic can also prove statements of the form `X = Y`, if `X` and
`Y` are definitionally equal--that is, equal by virtue of definitions.
"

/-- If your goal is a statement of the form `P ↔ Q`, and `P` and `Q` are definitionally
equivalent (that is, equivalent by virtue of the definitions of the symbols occurring in
them), then the `rfl` tactic will close the goal.  It will also close a goal of the form
`X = Y`, if `X` and `Y` are definitionally equal (that is, equal by virtue of definitions). -/
TacticDoc rfl

NewTactic rfl

/-- If `A` is a of objects from the universe `U`, then `Aᶜ` is the complement of `A`; that is,
`Aᶜ` is the set of objects from `U` that are not elements of `A`.  You can enter the symbol `ᶜ`
by typing `\compl` or `\^c`. -/
DefinitionDoc comp as "ᶜ"

/-- `P ↔ Q` means "P if and only if Q".  You can enter the symbol `↔` by typing `\iff`.

### If your goal is `P ↔ Q`

If `P` and `Q` are definitionally equivalent, then `rfl` will close the goal.
If you have `h1 : P → Q` and `h2 : Q → P`, then `Iff.intro h1 h2` is a proof of `P ↔ Q`,
so `exact Iff.intro h1 h2` will close the goal.
If you don't yet have proofs of `P → Q` and `Q → P`, then `apply Iff.intro` will set `P → Q`
and `Q → P` as your goals.  In this situation, the tactic `constructor` has the same effect as
`apply Iff.intro`.

### If you have an assumption `h : P ↔ Q`

Lean will recognize `h.mp` as a proof of `P → Q` and `h.mpr` as a proof of `Q → P`.  You may
also find it helpful to use `h` in the `rewrite` tactic.
-/
DefinitionDoc iff as "↔"

NewDefinition comp iff

TheoremTab "ᶜ"

/-- If you have `A : Set U` and `x : U`, then `mem_compl_iff A x` is a proof of the statement
`x ∈ Aᶜ ↔ x ∉ A`.  In Mathlib, the name of this theorem is `Set.mem_compl_iff`. -/
TheoremDoc STG4.mem_compl_iff as "mem_compl_iff" in "ᶜ"

/-- Let $x$ be an object in the universe $U$, and let $A$ be a set whose elements
come from $U$.  Then $x \in A^c \leftrightarrow x \notin A$. -/
Statement mem_compl_iff (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  Hint "The proof of the theorem in this level is very easy.
  Since `x ∈ Aᶜ` and `x ∉ A` are definitionally equivalent, `rfl` will close the goal."
  rfl

Conclusion
"
The name of the tactic `rfl` is short for \"reflexivity\", which is the property of
both `=` and `↔` that is the basis for the tactic.

We have given the theorem proven in this level the name `mem_compl_iff`.  In the next level,
we will see how we can use it to prove theorems about complements.
"
