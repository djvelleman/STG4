import Game.Levels.FamCombo.L02compinter

variable {U : Type}

World "FamCombo"
Level 3
Title "Two families with an element in common"

Introduction
"
This level is an exercise in handling sequences of quantifiers that alternate between
`∀` and `∃`.  A good way to start is to decide which assumption to use first.
"

/-- Suppose $F$ and $G$ are families of sets such that for every $A \in F$ there is some $B \in G$
such that $A \subseteq B$, and also there is some $A \in F$ such that for every $B \in G$,
$B \subseteq A$.  Then $F$ and $G$ have an element in common.-/
Statement (F G : Set (Set U)) (h1 : ∀ A ∈ F, ∃ B ∈ G, A ⊆ B) (h2 : ∃ A ∈ F, ∀ B ∈ G, B ⊆ A) :
    ∃ S, S ∈ F ∩ G := by
  obtain ⟨A, h3⟩ := h2
  have h4 := h1 A h3.left
  obtain ⟨B, h5⟩ := h4
  have h6 : B ⊆ A := h3.right B h5.left
  Hint (hidden := true) "Look at what you know about `{A}` and `{B}`."
  have h7 : A = B := sub_antisymm h5.right h6
  use A
  apply And.intro
  exact h3.left
  rewrite [h7]
  exact h5.left
