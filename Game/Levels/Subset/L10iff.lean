import Game.Levels.Subset.L09comp

variable {U : Type}

World "Subset"
Level 10
Title "Iff proofs"

Introduction
"
In this level, your goal is `A ⊆ B ↔ Bᶜ ⊆ Aᶜ`.  As we saw in a previous level, if you had
`h1 : A ⊆ B → Bᶜ ⊆ Aᶜ` and `h2 : Bᶜ ⊆ Aᶜ → A ⊆ B`, then `Iff.intro h1 h2` would prove the goal.
Unfortunately, you don't have such hypotheses `h1` and `h2`, and there doesn't seem to be an
easy way to justify asserting them.  To deal with this situation, we'll use a new tactic, `apply`.
If you write `apply Iff.intro`, then Lean will figure out that the theorem `Iff.intro` could be
applied to prove the goal, if only you had proofs of `A ⊆ B → Bᶜ ⊆ Aᶜ` and `Bᶜ ⊆ Aᶜ → A ⊆ B`.
So it will set these *two* statements as goals.
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

LemmaTab "Logic"

/-- Let $A$ and $B$ be sets.  Then $A \subseteq B$ if and only if $B^c \subseteq A^c$. -/
Statement (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  Hint "Your immediate goal now is to prove that `A ⊆ B → Bᶜ ⊆ Aᶜ`.  Once you close that goal,
  you'll be asked to prove the second goal, `Bᶜ ⊆ Aᶜ → A ⊆ B`.  You know everything you need
  to close the first goal."
  Hint (hidden := true) "You'll want to start with several applications of the `intro` tactic."
  intro h1 x h2
  Hint (hidden := true) "Now imitate the reasoning used in the previous level.
  If you don't remember that reasoning, try writing out the definition of
  \"complement\" in both an assumption and the goal."
  rewrite [comp_def]
  rewrite [comp_def] at h2
  Hint (hidden := true) "Now your goal is a negative statement.  That suggests a certain
  proof strategy."
  by_contra h3
  have h4 : x ∈ B := h1 h3
  exact h2 h4
  Hint "The second goal is similar."
  intro h1 x h2
  Hint "Although your goal is not a negative statement, do you see how assuming the opposite
  of the goal will lead to a contradiction?  That means that `by_contra` is once again a good idea."
  by_contra h3
  Hint "`comp_def x B` is a proof of `x ∈ Bᶜ ↔ x ∉ B`, so `rewrite [comp_def]` could be used to
  replace `x ∈ Bᶜ` with `x ∉ B`.  But now we'd like to do the opposite replacement: it would be
  helpful to change `{h3} : x ∉ B` to `{h3} : x ∈ Bᶜ`.  To do that, type
  `rewrite [← comp_def] at {h3}`.  (To enter the left-pointing arrow, type `\\l`.)"
  rewrite [← comp_def] at h3
  have h4 : x ∈ Aᶜ := h1 h3
  rewrite [comp_def] at h4
  exact h4 h2

Conclusion
"
In general, if `t` is a proof of an equivalence `P ↔ Q`, then `rewrite [← t]` will replace `Q`
in the goal with `P`, and you can add `at h` to do the replacement in an assumption `h`.

Congratulations on completing Subset World!  You're ready to move on to Intersection World.
"
