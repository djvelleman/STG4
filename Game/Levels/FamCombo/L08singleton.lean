import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "FamCombo"
Level 8
Title "A set that must be a singleton"

Introduction
"
The notation `{a}` denotes a set whose only element is `a`; such a set is called a *singleton*
set.  The theorem `mem_singleton_iff` expresses the definition of singleton sets: `mem_singleton_iff` is
a proof of any statement of the form `x ∈ {a} ↔ x = a`.
"

/-- Lean will recognize `mem_singleton_iff` is a proof of any statement of the form
`x ∈ {a} ↔ x = a`.  In Mathlib, the name of this theorem is `Set.mem_singleton_iff`. -/
TheoremDoc Set.mem_singleton_iff as "mem_singleton_iff" in "{ }"

NewTheorem Set.mem_singleton_iff

TheoremTab "{ }"

/-- Suppose $A$ is a set, and for every family of sets $F$, if $\bigcup F = A$ then $A \in F$.
Then $A$ must be a singleton set.-/
Statement (A : Set U) (h1 : ∀ F, (⋃₀ F = A → A ∈ F)) : ∃ x, A = {x} := by
  Hint (strict := true) "Start with `have h2 := h1 \{s | ...}`.  The hard part is figuring out
  how to fill in the `...`."
  Hint (strict := true) (hidden := true) "You need to apply `h1` to a family of sets with two
  properties: the union of the family must be `A`, and knowing that `A` belongs to the
  family must help you prove that `A` is a singleton."
  have h2 := h1 {s | ∃ x ∈ A, s = {x}}
  have h3 : ⋃₀ {s | ∃ x ∈ A, s = {x}} = A
  ext x
  apply Iff.intro
  intro h3
  obtain ⟨t, ht⟩ := h3
  rewrite [mem_setOf] at ht
  obtain ⟨y, hy⟩ := ht.left
  rewrite [hy.right] at ht
  rewrite [mem_singleton_iff] at ht
  rewrite [ht.right]
  exact hy.left
  intro h3
  use {x}
  apply And.intro
  rewrite [mem_setOf]
  use x
  rewrite [mem_singleton_iff]
  rfl
  have h4 := h2 h3
  rewrite [mem_setOf] at h4
  obtain ⟨y, hy⟩ := h4
  use y
  exact hy.right

Conclusion
"
Congratulations!  You have completed the Set Theory Game!

If you want to learn more about Lean, check out the [Lean Community](https://leanprover-community.github.io).
"
