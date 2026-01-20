import Game.Levels.FamInter.L03interpair

open Set

namespace STG4

variable {U : Type}

World "FamInter"
Level 4
Title "Intersection of a union of families"

Introduction
"
If `F` and `G` are families of sets, what is `⋂₀ (F ∪ G)`?  In this level, you'll find out!
"

/-- Suppose $F$ and $G$ are families of sets.  Then
$\bigcap (F \cup G) = (\bigcap F) \cap (\bigcap G)$. -/
Statement (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [mem_sInter] at h1
  rewrite [mem_inter_iff]
  apply And.intro
  rewrite [mem_sInter]
  intro t h2
  Hint "Here's an approach you might try:  If only you had `hFG : {t} ∈ F ∪ G`, then
  `{h1} {t} hFG` would prove the goal.  So if you use the tactic `apply {h1} {t}`, Lean
  will figure out that `{h1} {t}` could be applied to a proof of `{t} ∈ F ∪ G` to prove
  the goal, and it will therefore set `{t} ∈ F ∪ G` as your goal."
  apply h1 t
  rewrite [mem_union]
  exact Or.inl h2
  rewrite [mem_sInter]
  intro t h2
  apply h1 t
  exact Or.inr h2
  intro h1
  rewrite [mem_sInter]
  intro t h2
  rewrite [mem_inter_iff] at h1
  rewrite [mem_sInter, mem_sInter] at h1
  rewrite [mem_union] at h2
  rcases h2 with htF | htG
  exact h1.left t htF
  exact h1.right t htG
