import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "FamInter"
Level 2
Title "Intersection of larger family is smaller"

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
  rewrite [mem_sInter]
  rewrite [mem_sInter] at h2
  Hint "Now your goal starts with `∀ t`.  To prove it, you'll need to introduce
  a set `t` into the proof, using the tactic `intro t`.  Recall that the set `t` is
  *arbitrary*--that is, `t` could stand for any set--so whatever we prove about `t` will
  be true for *all* sets `t`."
  intro t
  Hint (hidden := true) "Now your goal is an if-then statement; that means `intro` is
  appropriate again, to introduce `{t} ∈ F` as a new assumption."
  intro h3
  Hint (hidden := true) "It looks like `{h2}` could get you to the goal, if only
  you knew that `{t} ∈ G`.  Can you prove that?"
  have h4 : t ∈ G := h1 h3
  Hint "You can now combine `{h2}` and `{h4}` to reach the goal in one step."
  Hint (hidden := true) "`{h2} {t} {h4}` is now a proof of the goal."
  exact h2 t h4

Conclusion
"
You probably used `intro` several times in this proof.  Recall that two `intro` steps in a row
can be combined into one step.  Click on `intro` in the list of tactics on the right for
further details.
"
