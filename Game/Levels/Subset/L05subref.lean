import Game.Levels.Subset.L04imp

open Set

namespace STG4

variable {U : Type}

World "Subset"
Level 5
Title "Subset is reflexive"

Introduction
"
How do you prove that one set is a subset of another?  To prove that `A ⊆ B`,
you have to show that if some object `x` is an element of `A`, then it is also
an element of `B`.  To do that, you'll have to introduce an object called `x` into
the proof.  The object denoted by `x` could be anything, so we say that it is
*arbitrary*.

In this level, we start with a simple example of this kind of proof.  We're going
to show that if `A` is a set, then `A ⊆ A`.
"

TheoremTab "⊆"

/-- If you have `A : Set U`, then `Subset.refl A` is a proof of `A ⊆ A`.
In Mathlib, the name of this theorem is `Set.Subset.refl`. -/
TheoremDoc STG4.Subset.refl as "Subset.refl" in "⊆"

/-- Let $A$ be any set.  Then $A \subseteq A$. -/
Statement Subset.refl (A : Set U) : A ⊆ A := by
  Hint "Our first step is to introduce an object `x` into the proof.  To do this, type `intro x`.
  We have already seen that the `intro` tactic can be used to introduce a new *assumption* into a
  proof.  This step illustrates a second use of `intro`: introducing a new *object* into a proof."
  intro x
  Hint "Notice that `{x} : U` has been added to the list of objects, and
  the goal has changed to `{x} ∈ A → {x} ∈ A`.  Fortunately, you already know how to prove
  a goal of this form."
  Hint (hidden := true) "Use `intro` again to introduce the assumption `{x} ∈ A`."
  intro h
  Hint "The situation now should remind you of your first proof, in level 1 of this world."
  Hint (hidden := true) "Notice that {h} is now a proof of the goal."
  exact h

Conclusion
"
The theorem you have proven in this level shows that the subset relation has
a property called *reflexivity*.  We have given the theorem the name `Subset.refl`.  You
will see it in the list of theorems on the right.  (This theorem is included in Lean's
mathematical library, Mathlib.  In Mathlib, the name of the theorem is `Set.Subset.refl`.
Many other set-theoretic theorems in this game have `Set.` at the beginnings of their names
in Mathlib.)
"
