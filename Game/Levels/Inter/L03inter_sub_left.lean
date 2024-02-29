import Game.Levels.Inter.L02elt_inter_elt_right

open Set

namespace STG4

variable {U : Type}

World "Intersection"
Level 3
Title "Intersection is a subset"

Introduction
"
You should be able to combine ideas from previous levels to solve this one.
"

/-- For any sets $A$ and $B$, $A \cap B \subseteq A$. -/
Statement (A B : Set U) : A ∩ B ⊆ A := by
  Hint (hidden := true) "Since the goal is a subset statement, you should start by
  introducing an object `x` and the assumption that `x ∈ A ∩ B`."
  intro x h
  rewrite [mem_inter_iff] at h
  exact h.left

Conclusion
"
You probably used a step like `rewrite [mem_inter_iff] at h` in this proof.  That step is
actually optional.  Writing out the definition of intersection probably helps *you*
understand how to proceed with the proof, but *Lean* doesn't need to be told to
write out the definition.  It will do that on its own.  In other words, if you
have `h : x ∈ A ∩ B`, Lean will accept `h.left` as a proof of `x ∈ A`.
"
