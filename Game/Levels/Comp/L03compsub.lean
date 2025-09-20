import Game.Metadata
import Game.Levels.Comp.L02compdef

open Set

namespace STG4

variable {U : Type}

World "Complement"
Level 3
Title "Complement subsets from subsets"

Introduction
"
In the last level, you proved the theorem `mem_compl_iff`.  If you have `A : Set U` and `x : U`,
then `mem_compl_iff A x` is a proof of the statement `x ∈ Aᶜ ↔ x ∉ A`.

You could think of the statement `x ∈ Aᶜ ↔ x ∉ A` as saying that if `x ∈ Aᶜ` occurs anywhere
in a proof, you can replace it with `x ∉ A`.  There is a tactic called `rewrite` that can be
used to perform such replacements.  You'll get to try out the `rewrite` tactic in this level.
"

/-- If the expression `t` is a proof of a statement of the form `P ↔ Q`, then the tactic
`rewrite [t]` will replace `P` anywhere that it occurs in the goal with `Q`.  If you want to
replace `Q` with `P`, use `rewrite [← t]`.  (Type `\l` to enter the symbol `←`.)  To do the
replacement in an assumption `h`, use `rewrite [t] at h`.

The `rewrite` tactic can also be used with equations.  If `t` is a proof of an equation
`p = q`, then `rewrite [t]` will replace `p` with `q` wherever it appears, and `rewrite [← t]`
will replace `q` with `p`.

To do multiple replacements, one after another, put a list of proofs inside the brackets, like
this:  `rewrite [t1, t2]`. -/
TacticDoc rewrite

NewTactic rewrite

TheoremTab "ᶜ"

/-- If you have `h : A ⊆ B`, then `compl_subset_compl_of_subset h` is a proof of `Bᶜ ⊆ Aᶜ`.
In Mathlib, the name of this theorem is `Set.compl_subset_compl_of_subset`. -/
TheoremDoc STG4.compl_subset_compl_of_subset as "compl_subset_compl_of_subset" in "ᶜ"

/-- Suppose $A \subseteq B$.  Then $B^c \subseteq A^c$. -/
Statement compl_subset_compl_of_subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  Hint "As usual, to prove a subset statement you need to introduce both a new object `x` and
  a new assumption `h2`.  You can do it in one step with `intro x h2`."
  intro x h2
  Hint "Now `mem_compl_iff A {x}` is a proof of the statement `{x} ∈ Aᶜ ↔ {x} ∉ A`, which tells us
  that we can reexpress the goal `{x} ∈ Aᶜ` as `{x} ∉ A`.  To do this reexpression,
  use the tactic `rewrite [mem_compl_iff A {x}]`."
  rewrite [mem_compl_iff A x]
  Hint "The `rewrite` tactic is smart enough to figure out some things on its own.  If you
  had just written `rewrite [mem_compl_iff]`, then Lean would have figured out how to apply the
  theorem `mem_compl_iff` to get an equivalence that could be used to make a replacement in the goal.
  In other words, it would have figured out that the theorem `mem_compl_iff` had to be applied to
  `A` and `{x}`.

  Similarly, you can write `rewrite [mem_compl_iff] at {h2}` to write out the meaning of `{h2}`.  Lean
  will figure out that in this case, `mem_compl_iff` has to be applied to `B` and `{x}`."
  rewrite [mem_compl_iff] at h2
  Hint (hidden := true) "Now your goal is a negative statement, so try proof by contradiction."
  by_contra h3
  Hint (hidden := true) "This should remind you of the first level of this world.  To get a contradiction,
  try to contradict `{h2} : {x} ∉ B`."
  have h4 : x ∈ B := h1 h3
  exact h2 h4

NewHiddenTactic rw

Conclusion
"
The `rewrite` tactic is often useful for writing out definitions.  For more information about
how it works, click on `rewrite` in the list of tactics on the right.  You can also use `rw`
instead of `rewrite`.  (There is actually a small difference between the tactics `rw` and
`rewrite`, but the difference won't concern us in this game.)

You'll find the theorem you proved in this level listed as `compl_subset_compl_of_subset` in the list of
theorems on the right.  This theorem will be useful in the last level of this world.
"
