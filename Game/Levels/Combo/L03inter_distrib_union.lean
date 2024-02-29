import Game.Levels.Combo.L02compint

open Set

namespace STG4

variable {U : Type}

World "Combination"
Level 3
Title "Intersection distributes over union"

Introduction
"
This proof is longer than previous ones, but it doesn't require any new tactics or theorems.
Just stick with it and keep applying the ideas from previous levels!
"

TheoremTab "∩∪"

/-- For any sets `A`, `B`, and `C`, `inter_distrib_left A B C` is a proof of the
statement `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.  In Mathlib, the name of this theorem
is `Set.inter_distrib_left`. -/
TheoremDoc STG4.inter_distrib_left as "inter_distrib_left" in "∩∪"

/-- For any sets $A$, $B$, and $C$, $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$. -/
Statement inter_distrib_left (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  Hint "Once again, Lean has left out some parentheses that it regards as unnecessary.
  Lean gives intersection higher precedence than union, so it interprets
  `A ∩ B ∪ A ∩ C` as `(A ∩ B) ∪ (A ∩ C)`."
  ext x
  apply Iff.intro
  intro h
  rewrite [mem_inter_iff] at h
  rewrite [mem_union]
  Hint (strict := true) (hidden := true) "It may help you see how to proceed if you separate
  out the second half of `{h}` as a separate assumption.
  You can do this with `have {h}BC : {x} ∈ B ∪ C := {h}.right`."
  have hBC : x ∈ B ∪ C := h.right
  rewrite [mem_union] at hBC
  cases' hBC with hB hC
  apply Or.inl
  exact And.intro h.left hB
  apply Or.inr
  exact And.intro h.left hC
  intro h
  rewrite [mem_union] at h
  rewrite [mem_inter_iff]
  cases' h with hB hC
  rewrite [mem_inter_iff] at hB
  apply And.intro
  exact hB.left
  rewrite [mem_union]
  exact Or.inl hB.right
  rewrite [mem_inter_iff] at hC
  apply And.intro
  exact hC.left
  rewrite [mem_union]
  exact Or.inr hC.right

Conclusion
"
Whew!
"
