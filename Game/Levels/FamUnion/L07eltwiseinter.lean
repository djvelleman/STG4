import Game.Levels.FamUnion.L06unionsub

open Set

namespace STG4

variable {U : Type}

World "FamUnion"
Level 7
Title "Union of a family of intersections"

Introduction
"
In this level, we introduce another way to define sets.  If `P x` is a statement about an
unspecified object `x`, then `{x | P x}` denotes the set of all values of `x` that make `P x`
come out true.  This is often called *set-builder notation*.  For example,
`{x | x ∈ A ∧ x ∈ B}` is another way to write `A ∩ B`.

As usual, we have a theorem that states the meaning of set-builder notation.  Lean will
recognize `mem_setOf` as a proof of any statement of the form `a ∈ {x | P x} ↔ P a`.
And that means that `rewrite [mem_setOf]` will rewrite `a ∈ {x | P x}` as `P a`.
"

/-- Lean will recognize `mem_setOf` as a proof of any statement of the form
`a ∈ {x | P x} ↔ P a`.  In Mathlib, the name of this theorem is `Set.mem_setOf`. -/
TheoremDoc Set.mem_setOf as "mem_setOf" in "{ }"

NewTheorem Set.mem_setOf

TheoremTab "{ }"

/--Suppose $A$ is a set and $F$ is a family of sets.  Then $A \cap (\bigcup F) =
\bigcup\{s \mid \exists u \in F, s = A \cap u\}$.-/
Statement (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x
  apply Iff.intro
  intro h1
  Hint (strict := true) "It will help to get as much information as you can out of `{h1}`
  before addressing the goal."
  Branch
    rewrite [mem_inter_iff] at h1
    Hint (strict := true) "You may find it useful to separate out the right half of `{h1}`.
    You can do that with `have {h1}r := {h1}.right`."
  have h2 : x ∈ ⋃₀ F := h1.right
  rewrite [mem_sUnion] at h2
  obtain ⟨t, ht⟩ := h2
  Branch
    rewrite [mem_inter_iff] at h1
    rewrite [mem_sUnion]
    Hint "Your goal is an existential statement.  Do you see what value to use as a witness?"
    Hint (hidden := true) "Try `apply Exists.intro (A ∩ {t})` or `use A ∩ {t}`."
  rewrite [mem_sUnion]
  Hint "Your goal is an existential statement.  Do you see what value to use as a witness?"
  Hint (hidden := true) "Try `apply Exists.intro (A ∩ {t})` or `use A ∩ {t}`."
  use A ∩ t
  apply And.intro
  Hint "You can use `rewrite [mem_setOf]` to write out the meaning of the goal."
  rewrite [mem_setOf]
  use t
  apply And.intro
  exact ht.left
  rfl
  exact And.intro h1.left ht.right
  intro h1
  Hint (strict := true) "Again, work out the consequences of `{h1}` first."
  obtain ⟨t, ht⟩ := h1
  Hint (strict := true) "You can separate out the first half of `{ht}` with `have {ht}l := {ht}.left`."
  have htl := ht.left
  rewrite [mem_setOf] at htl
  obtain ⟨u, hu⟩ := htl
  Hint (hidden := true) "You know `{x} ∈ {t}` and `{t} = A ∩ {u}`.  So you can use `rewrite`
  to get `{x} ∈ A ∩ {u}`."
  rewrite [hu.right, mem_inter_iff] at ht
  rewrite [mem_inter_iff]
  apply And.intro
  exact ht.right.left
  rewrite [mem_sUnion]
  use u
  exact And.intro hu.left ht.right.right
