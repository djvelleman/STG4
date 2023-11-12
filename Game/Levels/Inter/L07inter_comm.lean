import Game.Levels.Inter.L06inter_sub_swap

variable {U : Type}

World "Intersection"
Level 7
Title "Intersection is commutative"

Introduction
"
As we saw in Complement World, a good first step when your goal is an equation between
sets is `apply sub_antisymm`.  For the theorem in this level, that will leave you with
two goals: `A ∩ B ⊆ B ∩ A` and `B ∩ A ⊆ A ∩ B`.  Fortunately, you can prove *both* of these
goals by using the theorem `inter_sub_swap` from the last level.
"

LemmaTab "Set Theory"

LemmaDoc inter_comm as "inter_comm" in "Set Theory"
"For any sets `A` and `B`, `inter_comm A B` is a proof of the
statement `A ∩ B = B ∩ A`."

/-- For any sets $A$ and $B$, $A \cap B = B \cap A$. -/
Statement inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  apply sub_antisymm
  exact inter_sub_swap A B
  exact inter_sub_swap B A

NewLemma inter_comm

Conclusion
"
We'll prove one more property of intersections in the next level.
"
