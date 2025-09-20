import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "FamCombo"
Level 3
Title "Two families with an element in common"

Introduction
"
This level is an exercise in handling sequences of quantifiers that alternate between
`∀` and `∃`.  A good way to start is to decide which assumption to use first.
"

/-- Suppose $F$ and $G$ are families of sets such that for every $s \in F$ there is some $t \in G$
such that $s \subseteq t$, and also there is some $s \in F$ such that for every $t \in G$,
$t \subseteq s$.  Then $F$ and $G$ have an element in common.-/
Statement (F G : Set (Set U)) (h1 : ∀ s ∈ F, ∃ t ∈ G, s ⊆ t) (h2 : ∃ s ∈ F, ∀ t ∈ G, t ⊆ s) :
    ∃ u, u ∈ F ∩ G := by
  obtain ⟨s, h3⟩ := h2
  have h4 := h1 s h3.left
  obtain ⟨t, h5⟩ := h4
  have h6 : t ⊆ s := h3.right t h5.left
  Hint (hidden := true) "Look at what you know about `{s}` and `{t}`."
  have h7 : s = t := Subset.antisymm h5.right h6
  use s
  apply And.intro
  exact h3.left
  rewrite [h7]
  exact h5.left
