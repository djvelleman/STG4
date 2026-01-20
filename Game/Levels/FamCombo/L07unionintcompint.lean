import Game.Levels.FamCombo.L06unionintunion

open Set

namespace STG4

variable {U : Type}

World "FamCombo"
Level 7
Title "A union intersected with the complement of an intersection"

Introduction
"
This time we'll study the intersection of `(⋃₀ F)` and `(⋂₀ G)ᶜ`.
"

/-- Suppose $F$ and $G$ are families of sets.  Then $(\bigcup F) \cap (\bigcap G)^c \subseteq
\bigcup \{s \mid \exists u \in F, \exists v \in G, s = u \cap v^c\}$.-/
Statement (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ vᶜ} := by
  intro x h1
  have h1l := h1.left
  have h1r := h1.right
  rewrite [mem_sUnion] at h1l
  obtain ⟨u, hu⟩ := h1l
  rewrite [mem_compl_iff, mem_sInter] at h1r
  push_neg at h1r
  obtain ⟨v, hv⟩ := h1r
  rewrite [mem_sUnion]
  use u ∩ vᶜ
  apply And.intro
  rewrite [mem_setOf]
  use u
  apply And.intro
  exact hu.left
  use v
  apply And.intro
  exact hv.left
  rfl
  rewrite [mem_inter_iff, mem_compl_iff]
  exact And.intro hu.right hv.right
