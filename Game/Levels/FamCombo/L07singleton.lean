import Game.Levels.FamCombo.L06unionintcompint

variable {U : Type}

World "FamCombo"
Level 7
Title "A set that must be a singleton"

Introduction
"
The notation `{a}` denotes a set whose only element is `a`; such a set is called a *singleton*
set.  The theorem `single_def` expresses the definition of singleton sets: `single_def x a` is
a proof of the statement `x ∈ {a} ↔ x = a`.
"

lemma single_def (x a : U) : x ∈ {a} ↔ x = a := by rfl

LemmaDoc single_def as "single_def" in "{}"
"For any `x` and `a`, `single_def x a` is a proof of the statement `x ∈ {a} ↔ x = a`."

NewLemma single_def

LemmaTab "{}"

/-- Suppose $A$ is a set, and for every family of sets $F$, if $\bigcup F = A$ then $A \in F$.
Then $A$ must be a singleton set.-/
Statement (A : Set U) (h1 : ∀ F, (⋃₀ F = A → A ∈ F)) : ∃ x, A = {x} := by
  Hint (strict := true) "Start with `have h2 := h1 \{S | ...}`.  The hard part is figuring out
  how to fill in the `...`."
  Hint (strict := true) (hidden := true) "You need to apply h1 to a family of sets with two
  properties: the union of the family must be `A`, and knowing that `A` belongs to the
  family must help you prove that `A` is a singleton."
  have h2 := h1 {S | ∃ x ∈ A, S = {x}}
  have h3 : ⋃₀ {S | ∃ x ∈ A, S = {x}} = A
  ext x
  apply Iff.intro
  intro h3
  obtain ⟨S, hS⟩ := h3
  rewrite [set_builder_def] at hS
  obtain ⟨y, hy⟩ := hS.left
  rewrite [hy.right] at hS
  rewrite [single_def] at hS
  rewrite [hS.right]
  exact hy.left
  intro h3
  use {x}
  apply And.intro
  rewrite [set_builder_def]
  use x
  rewrite [single_def]
  rfl
  have h4 := h2 h3
  rewrite [set_builder_def] at h4
  obtain ⟨y, hy⟩ := h4
  use y
  exact hy.right
