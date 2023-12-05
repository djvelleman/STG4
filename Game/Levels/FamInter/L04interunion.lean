import Game.Levels.FamInter.L03interpair

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
  rewrite [fam_inter_def] at h1
  rewrite [inter_def]
  apply And.intro
  rewrite [fam_inter_def]
  intro S h2
  Hint "Here's an approach you might try:  If only you had `hFG : {S} ∈ F ∪ G`, then
  `{h1} {S} hFG` would prove the goal.  So if you use the tactic `apply {h1} {S}`, Lean
  will figure out that `{h1} {S}` could be applied to a proof of `{S} ∈ F ∪ G` to prove
  the goal, and it will therefore set `{S} ∈ F ∪ G` as your goal."
  apply h1 S
  rewrite [union_def]
  exact Or.inl h2
  rewrite [fam_inter_def]
  intro S h2
  apply h1 S
  exact Or.inr h2
  intro h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [inter_def] at h1
  rewrite [fam_inter_def, fam_inter_def] at h1
  rewrite [union_def] at h2
  cases' h2 with hSF hSG
  exact h1.left S hSF
  exact h1.right S hSG
