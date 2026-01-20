import Game.Levels.FamCombo.L04threefam

open Set

namespace STG4

variable {U : Type}

World "FamCombo"
Level 5
Title "A union intersected with the complement of another is a subset"

Introduction
"
What happens if you intersect `⋃₀ F` with `(⋃₀ G)ᶜ`, for two families `F` and `G`?
"

/-- Suppose $F$ and $G$ are families of sets.  Then $(\bigcup F) \cap (\bigcup G)^c \subseteq
\bigcup (F \cap G^c)$.-/
Statement (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x h1
  rewrite [mem_inter_iff] at h1
  have h1l := h1.left
  rewrite [mem_sUnion] at h1l
  obtain ⟨t, ht⟩ := h1l
  rewrite [mem_sUnion]
  use t
  apply And.intro
  rewrite [mem_inter_iff]
  apply And.intro
  exact ht.left
  rewrite [mem_compl_iff]
  by_contra h2
  have h1r := h1.right
  rewrite [mem_compl_iff, mem_sUnion] at h1r
  push_neg at h1r
  have hnt := h1r t h2
  exact hnt ht.right
  exact ht.right
