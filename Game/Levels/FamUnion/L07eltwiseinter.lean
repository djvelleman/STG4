import Game.Levels.FamUnion.L06unionsub

variable {U : Type}

World "FamUnion"
Level 7
Title "Union of a Family of Intersections"

Introduction
"
In this level, we introduce another way to define sets.  If `P x` is a statement about an
unspecified object `x`, then `{x | P x}` denotes the set of all values of `x` that make `P x`
come out true.  This is often called *set-builder notation*.  For example,
`{x | x ∈ A ∧ x ∈ B}` is another way to write `A ∩ B`.

As usual, we have a theorem that states the meaning of set-builder notation.  Lean will
recognize `set_builder_def` as a proof of any statement of the form `a ∈ {x | P x} ↔ P a`.
And that means that `rewrite [set_builder_def]` will rewrite `a ∈ {x | P x}` as `P a`.
"

lemma set_builder_def {P : U → Prop} {a : U} : a ∈ {x | P x} ↔ P a := by rfl

LemmaDoc set_builder_def as "set_builder_def" in "{}"
"
Lean will recognize `set_builder_def` as a proof of any statement of the form
`a ∈ {x | P x} ↔ P a`.
"

NewLemma set_builder_def

/--Suppose $A$ is a set and $F$ is a family of sets.  Then $A \cap (\bigcup F) =
\bigcup\{B \mid \exists S \in F, B = A \cap S\}$.-/
Statement (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {B | ∃ S ∈ F, B = A ∩ S} := by
  ext x
  apply Iff.intro
  intro h1
  Hint (strict := true) "It will help to get as much information as you can out of `{h1}`
  before addressing the goal."
  rewrite [inter_def] at h1
  Hint (strict := true) "You may find it useful to separate out the right half of `{h1}`.
  You can do that with `have {h1}r := {h1}.right`."
  have h2 : x ∈ ⋃₀ F := h1.right
  rewrite [fam_union_def] at h2
  cases' h2 with S hS
  rewrite [fam_union_def]
  Hint "Your goal is an existential statement.  Do you see what value to use as a witness?"
  Hint (hidden := true) "Try `apply Exists.intro (A ∩ S)` or `use A ∩ S`."
  use A ∩ S
  apply And.intro
  Hint "You can use `rewrite [set_builder_def]` to write out the meaning of the goal."
  rewrite [set_builder_def]
  use S
  apply And.intro hS.left
  rfl
  exact And.intro h1.left hS.right
  intro h1
  Hint (strict := true) "Again, work out the consequences of `{h1}` first."
  cases' h1 with B h1
  Hint (strict := true) "You can separate out the first half of `{h1}` with `have {h1}l := {h1}.left`."
  have h2 := h1.left
  rewrite [set_builder_def] at h2
  cases' h2 with S hS
  Hint (hidden := true) "You know `{x} ∈ {B}` and `{B} = A ∩ {S}`.  So you can use `rewrite`
  to get `{x} ∈ A ∩ {S}`."
  rewrite [inter_def]
  rewrite [hS.right, inter_def] at h1
  apply And.intro h1.right.left
  rewrite [fam_union_def]
  use S
  exact And.intro hS.left h1.right.right
