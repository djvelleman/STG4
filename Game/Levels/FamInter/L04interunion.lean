import Game.Levels.FamInter.L03interpair

variable {U : Type}

World "FamInter"
Level 4
Title "Intersection of a Union of Families"

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
  have h3 : S ∈ F ∪ G := Or.inl h2
  exact h1 S h3
  rewrite [fam_inter_def]
  intro S h2
  have h3 : S ∈ F ∪ G := Or.inr h2
  exact h1 S h3
  intro h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [inter_def] at h1
  have hxF := h1.left
  have hxG := h1.right
  rewrite [fam_inter_def] at hxF
  rewrite [fam_inter_def] at hxG
  rewrite [union_def] at h2
  cases' h2 with hSF hSG
  exact hxF S hSF
  exact hxG S hSG

Conclusion
"

"
