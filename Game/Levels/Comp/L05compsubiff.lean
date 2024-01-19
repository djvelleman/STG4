import Game.Levels.Comp.L04compcomp

variable {U : Type}

World "Complement"
Level 5
Title "Complement subsets equivalence"

Introduction
"
In this last level of Complement World, you'll prove a statement of the form `P ↔ Q`.  The most
useful theorem for this purpose is `Iff.intro`.  If you have `h1 : P → Q` and `h2 : Q → P`, then
`Iff.intro h1 h2` is a proof of `P ↔ Q`.  As we saw in the last level, that means you can start your
proof with `apply Iff.intro`.  Lean will set `P → Q` and `Q → P` as the goals that are needed
to complete the proof.
"

TheoremTab "ᶜ"

/-- If you have `h1 : P → Q` and `h2 : Q → P`, then `Iff.intro h1 h2` is a proof of `P ↔ Q`. -/
TheoremDoc Iff.intro as "Iff.intro" in "Logic"

NewTheorem Iff.intro

/-- Suppose $A$ and $B$ are sets.  Then $A \subseteq B$ if and only if $B^c \subseteq A^c$. -/
Statement (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  Hint "For the proof in this level, `apply Iff.intro` will create the goals `A ⊆ B → Bᶜ ⊆ Aᶜ`
  and `Bᶜ ⊆ Aᶜ → A ⊆ B`."
  apply Iff.intro
  Hint (hidden := true) "Of course, you should begin by introducing the assumption
  `h1 : A ⊆ B`."
  intro h1
  Hint "Fortunately, the theorem `comp_sub_of_sub` can now be used to prove the goal.
  (Click on `comp_sub_of_sub` in the list of theorems on the right if you don't
  remember what the theorem says.)"
  Hint (hidden := true) "`comp_sub_of_sub {h1}` will prove the goal."
  exact comp_sub_of_sub h1
  Hint "The second goal is similar, but a little trickier."
  intro h1
  Hint (strict := true) "The theorem `comp_sub_of_sub {h1}` doesn't prove the goal, but it comes close.
  Do you see what assertion it will justify?"
  Hint (strict := true) (hidden := true) "You can use `comp_sub_of_sub {h1}` to justify the assertion
  `Aᶜᶜ ⊆ Bᶜᶜ`."
  have h2 : Aᶜᶜ ⊆ Bᶜᶜ := comp_sub_of_sub h1
  Hint (strict := true) "Fortunately, we can use the theorem `comp_comp` to prove `Aᶜᶜ = A` and
  `Bᶜᶜ = B`, and those statements should get us from `{h2}` to the goal.
  We have seen in previous levels that the `rewrite` tactic can be applied to a proof of a
  statement of the form `P ↔ Q` to replace `P` with `Q`.  The tactic can also be applied to
  equations: if `t` is a proof of an equation `p = q`, then `rewrite [t]` will
  replace `p` with `q`."
  Hint (strict := true) (hidden := true) "`rewrite [comp_comp A] at {h2}` will change `Aᶜᶜ` to `A`, and
  `rewrite [comp_comp B] at {h2}` will change `Bᶜᶜ` to `B`.  In fact, you can do both
  rewrites in one step:  `rewrite [comp_comp A, comp_comp B] at {h2}`."
  rewrite [comp_comp A, comp_comp B] at h2
  exact h2

NewHiddenTactic constructor

Conclusion
"
The proof in this level illustrates how previously proven theorems can be used in proofs.

There is another tactic you can use if your goal has the form `P ↔ Q`.  In this situation,
the tactic `constructor` will have the same effect as `apply Iff.intro`; that is, it will
set `P → Q` and `Q → P` as goals to be proven.
"
