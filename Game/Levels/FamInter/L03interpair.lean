import Game.Levels.FamInter.L02intersubinter

open Set

namespace STG4

variable {U : Type}

World "FamInter"
Level 3
Title "Intersection of a pair"

Introduction
"
This level shows that family intersections are a generalization of the intersections
we studied in Intersection World.  You'll prove that if `A` and `B` are sets, then
`A ∩ B` is equal to the intersection of the family of sets that contains just `A` and
`B` and nothing else.

We'll need notation for the family of sets consisting of just `A` and `B`; we'll denote
this family by `{A, B}`.  And, as usual, we'll need a theorem stating the definition of
this notation.  For any `t`, `A`, and `B`, `mem_pair t A B` is a proof of the
statement `t ∈ {A, B} ↔ t = A ∨ t = B`.
"

lemma mem_pair (t A B : U) : t ∈ {A, B} ↔ t = A ∨ t = B := by rfl

/-- For any `t`, `A`, and `B`, `mem_pair t A B` is a proof of the statement
`t ∈ {A, B} ↔ t = A ∨ t = B`. -/
TheoremDoc STG4.mem_pair as "mem_pair" in "{}"

NewTheorem STG4.mem_pair

TheoremTab "{}"

/-- Suppose $A$ and $B$ are sets.  Then $A \cap B = \bigcap \{A, B\}$. -/
Statement (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [mem_inter_iff] at h1
  rewrite [mem_sInter]
  intro t h2
  rewrite [mem_pair] at h2
  cases' h2 with hA hB
  Hint "Now that you have `{hA} : {t} = A`, you can use `rewrite [{hA}]` to replace `{t}` with
  `A` in the goal."
  rewrite [hA]
  exact h1.left
  rewrite [hB]
  exact h1.right
  intro h1
  rewrite [mem_inter_iff]
  rewrite [mem_sInter] at h1
  apply And.intro
  Hint (strict := true) (hidden := true) "It would be helpful if you knew that `A ∈ \{A, B}`.
  You can use `have` to assert it."
  have h2 : A ∈ {A, B}
  rewrite [mem_pair]
  apply Or.inl
  rfl
  exact h1 A h2
  have h2 : B ∈ {A, B}
  rewrite [mem_pair]
  apply Or.inr
  rfl
  exact h1 B h2
