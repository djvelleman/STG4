import Game.Levels.FamUnion

variable {U : Type}

World "FamCombo"
Level 1
Title "Complement of a family union"

Introduction
"
In this level you'll prove a generalization of the theorem `comp_union` that you proved
in Combination World.  That theorem was about the complement of a union of two sets; the
theorem in this level is about the complement of a union of a family of sets.
"

/-- For any family of sets $F$, $(\bigcup F)^c = \bigcap \{A \mid A^c \in F\}$. -/
Statement (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {A | Aᶜ ∈ F} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [comp_def] at h1
  rewrite [set_builder_def] at h2
  Hint "Sometimes, if you don't see what else to do, proof by contradiction is a good
  thing to try, even if your goal is not a negative statement."
  by_contra h3
  Hint "Since `{h1}` is a negative statement, a good way to reach a contradiction
  would be to contradict it.  As we've seen before, `apply {h1}` will set the goal to be
  `{x} ∈ ⋃₀ F`."
  apply h1
  use Sᶜ
  apply And.intro h2
  rewrite [comp_def]
  exact h3
  intro h1
  rewrite [comp_def]
  by_contra h2
  rewrite [fam_union_def] at h2
  obtain ⟨S, hS⟩ := h2
  rewrite [fam_inter_def] at h1
  Hint (strict := true) "What set can you apply {h1} to?"
  have h3 : Sᶜ ∈ {A | Aᶜ ∈ F}
  rewrite [set_builder_def]
  rewrite [comp_comp]
  exact hS.left
  have h4 : x ∈ Sᶜ := h1 Sᶜ h3
  rewrite [comp_def] at h4
  exact h4 hS.right
