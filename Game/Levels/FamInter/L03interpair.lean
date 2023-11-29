import Game.Levels.FamInter.L02intersubinter

variable {U : Type}

World "FamInter"
Level 3
Title "Intersection of a Pair"

Introduction
"
This level shows that family intersections are a generalization of the intersections
we studied in Intersection World.  You'll prove that if `A` and `B` are sets, then
`A ∩ B` is equal to the intersection of the family of sets that contains just `A` and
`B` and nothing else.

We'll need notation for the family of sets consisting of just `A` and `B`; we'll denote
this family by `{A, B}`.  And, as usual, we'll need a theorem stating the definition of
this notation.  For any sets ``S`, `A`, and `B`, `pair_def S A B` is a proof of the
statement `S ∈ {A, B} ↔ S = A ∨ S = B`.
"

lemma pair_def (S A B : Set U) : S ∈ {A, B} ↔ S = A ∨ S = B := by rfl

LemmaDoc pair_def as "pair_def" in "{}"
"For any sets `S`, `A`, and `B`, `pair_def S A B` is a proof of the statement
`S ∈ {A, B} ↔ S = A ∨ S = B`."

NewLemma pair_def

LemmaTab "{}"

/-- Suppose $A$ and $B$ are sets.  Then $A \cap B = \bigcap \{A, B\}$. -/
Statement (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [inter_def] at h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [pair_def] at h2
  cases' h2 with hA hB
  rewrite [hA]
  exact h1.left
  rewrite [hB]
  exact h1.right
  intro h1
  rewrite [inter_def]
  rewrite [fam_inter_def] at h1
  apply And.intro
  have h2 : A ∈ {A, B}
  rewrite [pair_def]
  apply Or.inl
  rfl
  exact h1 A h2
  have h2 : B ∈ {A, B}
  rewrite [pair_def]
  apply Or.inr
  rfl
  exact h1 B h2

Conclusion
"

"
