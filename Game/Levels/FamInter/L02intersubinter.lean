import Game.Levels.FamInter.L01intersub

variable {U : Type}

World "FamInter"
Level 2
Title "Intersection of Larger Family is Smaller"

Introduction
"
In this level we have two families of sets, `F` and `G`, with `F ⊆ G`.  That means that
`⋂₀ G` is the intersection of a family of sets that includes all the sets in `F`, plus
perhaps more sets.  You're going to prove that intersecting this larger collection of sets
leads to a smaller result; more precisely, you're going to prove that `⋂₀ G ⊆ ⋂₀ F`.

Of course, by now you know how to start a proof that one set is a subset of another.
"

/-- Suppose $F$ and $G$ are families of sets and $F \subseteq G$.
Then $\bigcap G \subseteq \bigcap F$. -/
Statement (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h2
  Hint (hidden := true) "As usual, if you're not sure how to proceed then writing
  out definitions can help."
  rewrite [fam_inter_def]; rewrite [fam_inter_def] at h2
  Hint "Now your goal starts with `∀ S`.  To prove it, you'll need to introduce
  a set `S` into the proof, using the tactic `intro S`.  Recall that the set `S` is
  *arbitrary*--that is, `S` could stand for any set--so whatever we prove about `S` will
  be true for *all* sets `S`."
  intro S
  Hint (hidden := true) "Now your goal is an if-then statement; that means `intro` is
  appropriate again, to introduce `{S} ∈ F` as a new assumption."
  intro h3
  Hint (hidden := true) "It looks like `{h2}` could get you to the goal, if only
  you knew that `{S} ∈ G`.  Can you prove that?"
  have h4 : S ∈ G := h1 h3
  Hint "You can now combine {h2} and {h4} to reach the goal in one step."
  Hint (hidden := true) "`{h2} {S} {h4}` is now a proof of the goal."
  exact h2 S h4

Conclusion
"
Note that, as we saw in proofs that one set is a subset of another, the two `intro` steps
could be combined into one step.  Click on `intro` in the list of tactics on the right for
further details.
"
