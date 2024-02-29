import Game.Levels.FamUnion.L04unionpair

open Set

namespace STG4

variable {U : Type}

World "FamUnion"
Level 5
Title "Union of a union"

Introduction
"
In this level, `F` and `G` are families of sets, and you'll work out how `⋃₀ (F ∪ G)` is related
to `⋃₀ F` and `⋃₀ G`.
"

/-- Suppose $F$ and $G$ are families of sets.  Then $\bigcup (F \cup G) =
(\bigcup F) \cup (\bigcup G)$. -/
Statement (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [mem_sUnion] at h1
  obtain ⟨t, h1⟩ := h1
  rewrite [mem_union]
  rewrite [mem_union] at h1
  cases' h1.left with hF hG
  left
  rewrite [mem_sUnion]
  use t
  exact And.intro hF h1.right
  right
  use t
  exact And.intro hG h1.right
  intro h1
  rewrite [mem_union] at h1
  rewrite [mem_sUnion]
  cases' h1 with hF hG
  obtain ⟨t, h1⟩ := hF
  use t
  apply And.intro
  exact Or.inl h1.left
  exact h1.right
  obtain ⟨t, h1⟩ := hG
  use t
  apply And.intro
  exact Or.inr h1.left
  exact h1.right
