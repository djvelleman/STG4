import Game.Metadata
import Game.Levels.Inter.L06inter_sub_swap

open Set

namespace STG4

variable {U : Type}

World "Intersection"
Level 7
Title "Intersection is commutative"

Introduction
"
As we saw in Complement World, a good first step when your goal is an equation between
sets is `apply Subset.antisymm`.  For the theorem in this level, that will leave you with
two goals: `A ∩ B ⊆ B ∩ A` and `B ∩ A ⊆ A ∩ B`.  Fortunately, you can prove *both* of these
goals by using the theorem `inter_subset_swap` from the last level.
"

TheoremTab "∩∪"

/-- For any sets `A` and `B`, `inter_comm A B` is a proof of the
statement `A ∩ B = B ∩ A`.  In Mathlib, the name of this theorem is `Set.inter_comm`. -/
TheoremDoc STG4.inter_comm as "inter_comm" in "∩∪"

/-- For any sets $A$ and $B$, $A \cap B = B \cap A$. -/
Statement inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  apply Subset.antisymm
  exact inter_subset_swap A B
  exact inter_subset_swap B A

Conclusion
"
We'll prove one more property of intersections in the next level.
"
