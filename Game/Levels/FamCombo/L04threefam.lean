import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "FamCombo"
Level 4
Title "A theorem about three families"

Introduction
"
Here's a theorem about three related families of sets.
"

/-- Suppose that for every $s \in F$ there is some $u \in G$ such that $s \cap u \in H$.
Then $(\bigcup F) \cap (\bigcap G) \subseteq \bigcup H$. -/
Statement (F G H : Set (Set U)) (h1 : ∀ s ∈ F, ∃ u ∈ G, s ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x h2
  rewrite [mem_inter_iff] at h2
  have h2l := h2.left
  have h2r := h2.right
  rewrite [mem_sUnion] at h2l
  obtain ⟨t, ht⟩ := h2l
  have h3 := h1 t ht.left
  obtain ⟨u, hu⟩ := h3
  rewrite [mem_sInter] at h2r
  have h3 := h2r u hu.left
  rewrite [mem_sUnion]
  use t ∩ u
  apply And.intro hu.right
  rewrite [mem_inter_iff]
  exact And.intro ht.right h3
