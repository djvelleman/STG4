import Game.Metadata
import Game.Levels.Comp

open Set

namespace STG4

variable {U : Type}

World "FamCombo"
Level 6
Title "A subset of a union intersected with the complement of another"

Introduction
"
What happens if the subset statement in the last level is reversed?
"

/-- Suppose $F$ and $G$ are families of sets and $\bigcup (F \cap G^c) \subseteq (\bigcup F)
\cap (\bigcup G)^c$.  Then $(\bigcup F) \cap (\bigcup G) \subseteq \bigcup (F \cap G)$.-/
Statement (F G : Set (Set U)) (h1 : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  intro x h2
  have h2l := h2.left
  have h2r := h2.right
  rewrite [mem_sUnion] at h2l
  obtain ⟨t, ht⟩ := h2l
  use t
  apply And.intro
  apply And.intro
  exact ht.left
  by_contra h3
  have h4 : x ∈ ⋃₀ (F ∩ Gᶜ)
  use t
  apply And.intro
  apply And.intro
  exact ht.left
  rewrite [mem_compl_iff]
  exact h3
  exact ht.right
  have h5 := h1 h4
  have h5r := h5.right
  rewrite [mem_compl_iff] at h5r
  exact h5r h2r
  exact ht.right
