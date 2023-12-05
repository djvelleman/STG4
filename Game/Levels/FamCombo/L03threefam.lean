import Game.Levels.FamCombo.L02compinter

variable {U : Type}

World "FamCombo"
Level 3
Title "A theorem about three families"

Introduction
"
Here's a theorem about three related families of sets.
"

/-- Suppose that for every $A \in F$ there is some $B \in G$ such that $A \cap B \in H$.
Then $(\bigcup F) \cap (\bigcap G) \subseteq \bigcup H$. -/
Statement (F G H : Set (Set U)) (h1 : ∀ A ∈ F, ∃ B ∈ G, A ∩ B ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x h2
  rewrite [inter_def] at h2
  have h2l := h2.left
  have h2r := h2.right
  rewrite [fam_union_def] at h2l
  cases' h2l with A hA
  have h3 := h1 A hA.left
  cases' h3 with B hB
  rewrite [fam_inter_def] at h2r
  have h3 := h2r B hB.left
  rewrite [fam_union_def]
  use A ∩ B
  apply And.intro hB.right
  rewrite [inter_def]
  exact And.intro hA.right h3
