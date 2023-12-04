import Game.Levels.FamUnion.L01proveexists

variable {U : Type}

World "FamUnion"
Level 2
Title "Subset of Family Union"

Introduction
"
In mathematical writing, the union of the family $F$ is usually denoted $\\bigcup F$.
In Lean, the union of a family `F` is denoted `⋃₀ F`.  (You can enter the symbol
`⋃₀` by typing `\\U0`.)

Suppose we have `F : Set (Set U)` and `x : U`.  Then `x ∈ ⋃₀ F` means that there is at least
one set `S` such that `S ∈ F` and `x ∈ S`.  To write this statement in Lean, we write
`∃ S, S ∈ F ∧ x ∈ S`.  Lean abbreviates this statement as `∃ S ∈ F, x ∈ S`.

As with other set theory operations, we have a theorem that expresses this definition.  If
`F : Set (Set U)` and `x : U`, then `fam_union_def x F` is a proof of the statement
`x ∈ ⋃₀ F ↔ ∃ S ∈ F, x ∈ S`.

In this level, you'll try out these ideas.
"

DefinitionDoc famunion as "⋃₀"
"`⋃₀ F` is the union of the family of sets `F`.  To enter the symbol `⋃₀`, type `\\U0`."

NewDefinition famunion

lemma fam_union_def (x : U) (F : Set (Set U)) : x ∈ ⋃₀ F ↔ ∃ S ∈ F, x ∈ S := by rfl

LemmaDoc fam_union_def as "fam_union_def" in "⋂₀⋃₀"
"If `F : Set (Set U)` and `x : U`, then `fam_union_def x F` is a proof of the statement
`x ∈ ⋃₀ F ↔ ∃ S ∈ F, x ∈ S`."

NewLemma fam_union_def

TacticDoc use
"
If your goal is `∃ x, P x`, where `P x` represents some statement about `x`, and `a` is a
value that could be assigned to `x`, then the tactic `use a` will
set `P a` to be the goal.  It will then see if this new goal follows easily from your
assumptions, and if so it will close the goal.
"

NewTactic use

LemmaTab "⋂₀⋃₀"

/-- Suppose $F$ is a family of sets and $A \in F$.  Then $A \subseteq \bigcup F$. -/
Statement (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x h2
  rewrite [fam_union_def]
  Hint "Remember that the goal `∃ S ∈ F, {x} ∈ S` is an abbreviation for
  `∃ S, S ∈ F ∧ {x} ∈ S`.  As we saw in the last level, we can prove this by coming up with
  a witness--that is, a value for `S` that will make the statement `S ∈ F ∧ {x} ∈ S` come out
  true.  Looking at
  `h1` and `{h2}`, it looks like `S = A` would work.  That suggests a way to proceed:
  `Exists.intro A hA` would prove the goal, if `hA` were a proof of `A ∈ F ∧ {x} ∈ A`.  In
  other words, if `Exists.intro A` is applied to a proof of `A ∈ F ∧ {x} ∈ A`, then it will
  prove the goal.  So if you use the tactic `apply Exists.intro A`, then Lean will
  set `A ∈ F ∧ {x} ∈ A` as your new goal."
  apply Exists.intro A
  exact And.intro h1 h2

Conclusion
"
There is another tactic you could have used to complete this proof.  Instead of
`apply Exists.intro A`, you could write `use A`.  The `use` tactic is actually a powerful
tactic.  Not only does it fill in `A` for `S` in the existential goal, it then tries to
complete the proof on its own--and in this case, it would have succeeded!
"
