import Game.Metadata
import Game.Levels.Comp

open Set

namespace STG4

variable {U : Type}

World "FamCombo"
Level 2
Title "Complement of a family intersection"

Introduction
"
Perhaps you have already guessed that there is a theorem about the complement
of an intersection of a family that is similar to the theorem in the last level.
"

/-- For any family of sets $F$, $(\bigcap F)^c = \bigcup \{s \mid s^c \in F\}$. -/
Statement (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {s | sᶜ ∈ F} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [mem_compl_iff] at h1
  Branch
    rewrite [mem_sUnion]
    by_contra h2
    Hint (strict := true) "What statement would you like to contradict to complete the proof?"
    apply h1
    rewrite [mem_sInter]
    intro t h3
    by_contra h4
    Hint "Now what statement would you like to contradict to complete the proof?"
  Branch
    by_contra h2
    Hint (strict := true) "What statement would you like to contradict to complete the proof?"
    apply h1
    rewrite [mem_sInter]
    intro t h3
    by_contra h4
    Hint "Now what statement would you like to contradict to complete the proof?"
  rewrite [mem_sInter] at h1
  push_neg at h1
  obtain ⟨t, ht⟩ := h1
  use tᶜ
  rewrite [mem_setOf, compl_compl, mem_compl_iff]
  exact ht
  intro h1
  rewrite [mem_compl_iff, mem_sInter]
  push_neg
  rewrite [mem_sUnion] at h1
  obtain ⟨u, hu⟩ := h1
  use uᶜ
  apply And.intro
  rewrite [mem_setOf] at hu
  exact hu.left
  rewrite [mem_compl_iff]
  push_neg
  exact hu.right
