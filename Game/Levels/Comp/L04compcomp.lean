import Game.Levels.Comp.L03compsub

open Set

namespace STG4

variable {U : Type}

World "Complement"
Level 4
Title "Complement of a complement"

Introduction
"
How do we prove that two sets `A` and `B` are equal?  One way to do it is to use the theorem
`Subset.antisymm`.  This theorem is pre-defined in this game; you don't need to prove it.
If you have `h1 : A ⊆ B` and `h2 : B ⊆ A`, then
`Subset.antisymm h1 h2` is a proof of `A = B`.  The theorem `Subset.antisymm` says that the
subset relation has a property called *antisymmetry*.

But what if you don't already know `A ⊆ B` and `B ⊆ A`?  In that case, you can use a new
tactic, `apply`.  If your goal is `A = B` and you write `apply Subset.antisymm`, then Lean will
figure out that the theorem `Subset.antisymm` could be applied to prove the goal, if only you had
proofs of `A ⊆ B` and `B ⊆ A`.  So it will set those *two* statements as goals.

If your goal says that two sets are equal, a good way to begin is with
`apply Subset.antisymm`.  (Later we'll see a second approach to proving sets are equal.)

This level also introduces another new tactic, `push_neg`.
"

/-- You can use the `apply` tactic to work backwards from the goal.  Suppose you think that you
will be able to use some theorem `t` to prove the goal.  In other words, you think there
is a proof of the goal of the form `t ?`, where the question mark needs to be replaced
with a proof of some statement `P` to which the theorem `t` must be applied.  The tactic
`apply t` will then set `P` as your goal.  If `t` must be applied to more than one proof to
establish the goal, then `apply t` will set all of the needed proofs as goals. -/
TacticDoc apply

/-- If your goal is a negative statement, then the tactic `push_neg` will try to reexpress it as
an equivalent positive statement.  Similarly, if an assumption `h` is a negative
statement, then `push_neg at h` will try to reexpress `h`.  Here are some examples of
reexpressions performed by the `push_neg` tactic:
* `¬¬P` is converted to `P`.
* `¬(P ∨ Q)` is converted to `¬P ∧ ¬Q`.
* `¬(P ∧ Q)` is converted to `P → ¬Q`.
* `¬(P → Q)` is converted to `P ∧ ¬Q`.
* `¬∀ x, P x` is converted to `∃ x, ¬P x`.
* `¬∃ x, P x` is converted to `∀ x, ¬P x`.
-/
TacticDoc push_neg

NewTactic apply push_neg

TheoremTab "⊆"

/-- If you have `h1 : A ⊆ B` and `h2 : B ⊆ A`, then `Subset.antisymm h1 h2` is a proof of `A = B`.
In Mathlib, the name of this theorem is `Set.Subset.antisymm`. -/
TheoremDoc Set.Subset.antisymm as "Subset.antisymm" in "⊆"

NewTheorem Set.Subset.antisymm

/-- If `A` is a set, then `compl_compl A` is a proof of `Aᶜᶜ = A`. -/
TheoremDoc compl_compl as "compl_compl" in "ᶜ"

/-- Suppose $A$ is a set.  Then $(A^c)^c = A$. -/
Statement compl_compl (A : Set U) : Aᶜᶜ = A := by
  Hint "In this level, your goal is `Aᶜᶜ = A`--that is, the complement of `Aᶜ` is equal to `A`.
  So `apply Subset.antisymm` is a good way to start."
  apply Subset.antisymm
  Hint "Your immediate goal now is to prove that `Aᶜᶜ ⊆ A`.  Once you close that goal,
  you'll be asked to prove the second goal, `A ⊆ Aᶜᶜ`."
  intro x h1
  Hint "Now write out the definition of complement in `{h1}`."
  rewrite [mem_compl_iff] at h1
  Hint "The assumption `{h1}` now says `{x} ∉ Aᶜ`, which means `¬{x} ∈ Aᶜ`.  It will be helpful to
  write out the definition of complement again in this assumption."
  rewrite [mem_compl_iff] at h1
  Hint "Now `{h1}` says `¬{x} ∉ A`, which means `¬¬{x} ∈ A`.  Of course, this can be simplified to
  `{x} ∈ A`.  To perform this simplification, you'll need a new tactic, `push_neg`.  To simplify
  the assumption `{h1}`, write `push_neg at {h1}`."
  push_neg at h1
  exact h1
  Hint "The proof of the second goal is similar."
  intro x h1
  rewrite [mem_compl_iff]
  Hint "There are two ways to complete the proof now.  Since your goal is a negative statement,
  one natural strategy to use would be proof by contradiction.  A second possibility is to
  imitate the approach in the first half: write out the meaning of complement again in the goal,
  and then use the `push_neg` tactic to simplify the resulting double-negative goal.  Either
  approach will work."
  rewrite [mem_compl_iff]
  push_neg
  exact h1

Conclusion
"
The `push_neg` tactic can reexpress a number of different kinds of negative statements as
equivalent positive statements; use
`push_neg` to reexpress a negative goal, and `push_neg at h` to reexpress a negative assumption `h`.
We'll see many more uses of the `apply` tactic in this game.
For more details about the use of these tactics,
click on `push_neg` or `apply` under the list of tactics on the right.

We have given this theorem the name `compl_compl`.  Both this theorem and the one in the previous
level will be useful in the next level.
"
