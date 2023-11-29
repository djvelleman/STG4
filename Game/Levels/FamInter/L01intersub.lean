import Game.Levels.Combo

variable {U : Type}

World "FamInter"
Level 1
Title "Family Intersection is Subset"

Introduction
"
In mathematical writing, the intersection of the family $F$ is usually denoted $\\bigcap F$.
In Lean, the intersection of a family `F` is denoted `⋂₀ F`.  (You can enter the symbol
`⋂₀` by typing `\\I0`.)

Suppose we have `F : Set (Set U)` and `x : U`.  Then `x ∈ ⋂₀ F` means that for every set `S`, if
`S` is in `F`, then `x ∈ S`.  To write this statement in Lean, we write `∀ S, S ∈ F → x ∈ S`.
Lean abbreviates this statement as `∀ S ∈ F, x ∈ S`.
The symbol `∀` is called the *universal quantifier*, and you can enter it in Lean by typing
`\\forall`.

As with other set theory operations, we have a theorem that expresses this definition.  If
`F : Set (Set U)` and `x : U`, then `fam_inter_def x F` is a proof of the statement
`x ∈ ⋂₀ F ↔ ∀ S ∈ F, x ∈ S`.

In this level, you'll try out these ideas.
"

DefinitionDoc famint as "⋂₀"
"`⋂₀ F` is the intersection of the family of sets `F`.  To enter the symbol `⋂₀`, type `\\I0`."

DefinitionDoc all as "∀"
"`∀ x, ...` means \"for all `x`, ...\".  To enter the symbol `∀`, type `\\forall`."

NewDefinition famint all

lemma fam_inter_def (x : U) (F : Set (Set U)) : x ∈ ⋂₀ F ↔ ∀ S ∈ F, x ∈ S := by rfl

LemmaDoc fam_inter_def as "fam_inter_def" in "⋂₀⋃₀"
"If `F : Set (Set U)` and `x : U`, then `fam_inter_def x F` is a proof of the statement
`x ∈ ⋂₀ F ↔ ∀ S ∈ F, x ∈ S`."

NewLemma fam_inter_def

LemmaTab "⋂₀⋃₀"

/-- Suppose $F$ is a family of sets and $A \in F$.  Then $\bigcap F \subseteq A$. -/
Statement (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x h2
  Hint "As usual, you may find it helpful to use the `rewrite` tactic to write out the
  definition of `{x} ∈ ⋂₀ F`, using the theorem `fam_inter_def`."
  rewrite [fam_inter_def] at h2
  Hint "Remember that `{h2} : ∀ S ∈ F, {x} ∈ S` is an abbreviation for
  `{h2} : ∀ S, S ∈ F → {x} ∈ S`.  Since `∀` means \"for all\", `{h2}` can be applied to any
  set--that is, we can plug in any set for `S` in `{h2}`.
  In particular, applying it to the set `A`, we can conclude that `A ∈ F → {x} ∈ A`.
  To apply `{h2}` to `A`, we just write `{h2}` followed by `A`, with a space between them.
  Thus, your next step can be `have h3 : A ∈ F → {x} ∈ A := {h2} A`."
  have h3 : A ∈ F → x ∈ A := h2 A
  Hint "Since we also have `h1 : A ∈ F`, you can apply `{h3}` to `h1` to prove that `{x} ∈ A`.
  This means that `{h3} h1` is a proof of the goal."
  exact h3 h1


Conclusion
"
The last two steps could have been combined into one step.  In general, if you have
`h1 : A ∈ F` and `h2 : ∀ S ∈ F, ...S...`, then `h2 A` is a proof of `A ∈ F → ...A...`, and
applying that proof to `h1` we conclude that `h2 A h1` is a proof of `...A...`.
"
