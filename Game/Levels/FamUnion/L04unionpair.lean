import Game.Levels.FamUnion.L03unionsubunion

variable {U : Type}

World "FamUnion"
Level 4
Title "Union of a pair"

Introduction
"
In this level, you'll show that, as with intersections, family unions generalize the
unions we studied in Union World.
"

/-- Suppose $A$ and $B$ are sets.  Then $A \cup B = \bigcup \{A, B\}$. -/
Statement (A B : Set U) : A ∪ B = ⋃₀ {A, B}:= by
  ext x
  apply Iff.intro
  intro h1
  rewrite [fam_union_def]
  rewrite [union_def] at h1
  cases' h1 with hA hB
  use A
  apply And.intro
  rewrite [pair_def]
  apply Or.inl
  rfl
  exact hA
  use B
  apply And.intro
  rewrite [pair_def]
  right
  rfl
  exact hB
  intro h1
  rewrite [union_def]
  rewrite [fam_union_def] at h1
  Hint "Remember, you can use `obtain` to introduce a name for the set that is asserted to
  exist in `{h1}`."
  obtain ⟨S, hS⟩ := h1
  rewrite [pair_def] at hS
  cases' hS.left with hA hB
  rewrite [hA] at hS
  exact Or.inl hS.right
  rewrite [hB] at hS
  exact Or.inr hS.right
