import Game.Levels.Comp.L03compsub

variable {U : Type}

World "Complement"
Level 4
Title "Complement of a complement"

Introduction
"
How do we prove that two sets `A` and `B` are equal?  One way to do it is to use the theorem
`sub_antisymm`.  This theorem is pre-defined in this game; you don't need to prove it.
If you have `h1 : A ⊆ B` and `h2 : B ⊆ A`, then
`sub_antisymm h1 h2` is a proof of `A = B`.  The theorem `sub_antisymm` says that the
subset relation has a property called *antisymmetry*.

But what if you don't already know `A ⊆ B` and `B ⊆ A`?  In that case, you can use a new
tactic, `apply`.  If your goal is `A = B` and you write `apply sub_antisymm`, then Lean will
figure out that the theorem `sub_antisymm` could be applied to prove the goal, if only you had
proofs of `A ⊆ B` and `B ⊆ A`.  So it will set those *two* statements as goals.

If your goal says that two sets are equal, a good way to begin is with
`apply sub_antisymm`.  (Later we'll see a second approach to proving sets are equal.)
"

TacticDoc apply
"
You can use the `apply` tactic to work backwards from the goal.  Suppose you think that you
will be able to use some theorem `t` to prove the goal.  In other words, you think there
is a proof of the goal of the form `t ?`, where the question mark needs to be replaced
with a proof of some statement `P` to which the theorem `t` must be applied.  The tactic
`apply t` will then set `P` as your goal.  If `t` must be applied to more than one proof to
establish the goal, then `apply t` will set all of the needed proofs as goals.
"

NewTactic apply

LemmaTab "Set Theory"

lemma sub_antisymm {A B : Set U} (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B := Set.Subset.antisymm h1 h2

LemmaDoc sub_antisymm as "sub_antisymm" in "Set Theory"
"If you have `h1 : A ⊆ B` and `h2 : B ⊆ A`, then `sub_antisymm h1 h2` is a proof of `A = B`."

LemmaDoc comp_comp as "comp_comp" in "Set Theory"
"If `A` is a set, then `comp_comp A` is a proof of `Aᶜᶜ = A`."

/-- Suppose $A$ is a set.  Then $(A^c)^c = A$. -/
Statement comp_comp (A : Set U) : Aᶜᶜ = A := by
  Hint "In this level, your goal is `Aᶜᶜ = A`--that is, the complement of `Aᶜ` is equal to `A`.
  So `apply sub_antisymm` is a good way to start."
  apply sub_antisymm
  Hint "Your immediate goal now is to prove that `Aᶜᶜ ⊆ A`.  Once you close that goal,
  you'll be asked to prove the second goal, `A ⊆ Aᶜᶜ`."
  intro x h1
  Hint (hidden := true) "Try writing out the definition of complement in {h1}."
  rewrite [comp_def] at h1
  Hint "Even though your goal is not a negative statement, the assumption `{h1}` is now the
  negative statement `{x} ∉ Aᶜ`.  This suggests that proof by
  contradiction might work: if you assume the opposite of the goal, you might be able to
  achieve a contradiction by proving `{x} ∈ Aᶜ`."
  by_contra h2
  Hint "Can you prove `{x} ∈ Aᶜ` from your new assumption `{h2} : {x} ∉ A`?  The tactic
  `rewrite [comp_def] at {h2}` would rewrite `{x} ∈ Aᶜ` as `{x} ∉ A`, but we want to go in
  the opposite direction, rewriting `{x} ∉ A` as `{x} ∈ Aᶜ`.  To do that, use
  `rewrite [← comp_def] at {h2}`.  (To enter the left-pointing arrow, type `\\l`.)"
  rewrite [← comp_def] at h2
  exact h1 h2
  Hint "The proof of the second goal is similar."
  intro x h1
  rewrite [comp_def]
  by_contra h2
  rewrite [comp_def] at h2
  exact h2 h1

NewLemma sub_antisymm comp_comp

Conclusion
"
We'll see many more uses of the `apply` tactic.  For more details about the use of the tactic,
click on `apply` under the list of tactics on the right.

We have given this theorem the name `comp_comp`.  Both this theorem and the one in the previous
level will be useful in the next level.
"
