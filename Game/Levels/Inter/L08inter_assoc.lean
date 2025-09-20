import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Intersection"
Level 8
Title "Intersection is associative"

Introduction
"
Our goal in this level is again an equation between sets.  In previous proofs of this kind,
we've started with the tactic `apply Subset.antisymm`, and that would work here as well.
But we're going to try out an alternative: the tactic `ext`.  This tactic applies the principle
of *extensionality* for sets, which says that if
two sets have exactly the same elements, then they are equal.
"

TheoremTab "∩∪"

/-- For any sets `A`, `B`, and `C`, `inter_assoc A B C` is a proof of the
statement `(A ∩ B) ∩ C = A ∩ (B ∩ C)`.  Im Mathlib, the name of this theorem is `Set.inter_assoc`. -/
TheoremDoc STG4.inter_assoc as "inter_assoc" in "∩∪"

/-- If your goal is `A = B`, where `A` and `B` are sets, then the tactic `ext x` will introduce
a new arbitrary object `x` into the proof and set the goal to be `x ∈ A ↔ x ∈ B`. -/
TacticDoc ext

NewTactic ext

/-- For any sets $A$, $B$, and $C$, $(A \cap B) \cap C = A \cap (B \cap C)$. -/
Statement inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  Hint "Notice that Lean has written the goal as `A ∩ B ∩ C = A ∩ (B ∩ C)`, with no
  parentheses on the left.  When an intersection of more than two sets is written
  without parentheses, Lean groups the intersections to the left, so this means
  `(A ∩ B) ∩ C = A ∩ (B ∩ C)`.

  To start this proof, use the tactic `ext x`."
  ext x
  Hint "Notice that Lean has introduced the new object `{x} : U` into the proof, and
  your goal is now `{x} ∈ A ∩ B ∩ C ↔ {x} ∈ A ∩ (B ∩ C)`.  Proving this goal will show that
  `A ∩ B ∩ C` and `A ∩ (B ∩ C)` have exactly the same elements, and by the principle of
  extensionality, that will show that the sets are equal."
  Hint (hidden := true) "Since your goal is an \"if and only if\" statement, a good next step
  is `apply Iff.intro`."
  apply Iff.intro
  Hint (hidden := true) "Since your goal is an \"if-then\" statement, a good next step
  is `intro h1`."
  intro h1
  rewrite [mem_inter_iff]
  rewrite [mem_inter_iff] at h1
  Hint (strict := true) (hidden := true) "If you're stuck at this point,
  it may help you see how to proceed if you separate
  out the first half of `{h1}` as a separate assumption.
  You can do this with `have hAB : {x} ∈ A ∩ B := {h1}.left`."
  have hAB : x ∈ A ∩ B := h1.left
  rewrite [mem_inter_iff] at hAB
  apply And.intro
  exact hAB.left
  exact And.intro hAB.right h1.right
  intro h1
  apply And.intro
  exact And.intro h1.left h1.right.left
  exact h1.right.right

Conclusion
"
Well done!  You're ready to move on to Union World.
"
