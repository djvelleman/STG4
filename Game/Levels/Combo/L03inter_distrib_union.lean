import Game.Levels.Combo.L02compint

variable {U : Type}

World "Combination"
Level 3
Title "Intersection distributes over union"

Introduction
"
This proof is longer than previous ones, but it doesn't require any new tactics or theorems.
Just stick with it and keep applying the ideas from previous levels!
"

LemmaTab "∩∪"

LemmaDoc inter_distrib_over_union as "inter_distrib_over_union" in "∩∪"
"For any sets `A`, `B`, and `C`, `inter_distrib_over_union A B C` is a proof of the
statement `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`."

/-- For any sets $A$, $B$, and $C$, $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$. -/
Statement inter_distrib_over_union (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  apply Iff.intro
  intro h
  rewrite [inter_def] at h
  rewrite [union_def]
  Hint (strict := true) (hidden := true) "It may help you see how to proceed if you separate
  out the second half of `{h}` as a separate assumption.
  You can do this with `have {h}BC : {x} ∈ B ∪ C := {h}.right`."
  have hBC : x ∈ B ∪ C := h.right
  rewrite [union_def] at hBC
  cases' hBC with hB hC
  apply Or.inl
  exact And.intro h.left hB
  apply Or.inr
  exact And.intro h.left hC
  intro h
  rewrite [union_def] at h
  rewrite [inter_def]
  cases' h with hB hC
  rewrite [inter_def] at hB
  apply And.intro
  exact hB.left
  rewrite [union_def]
  exact Or.inl hB.right
  rewrite [inter_def] at hC
  apply And.intro
  exact hC.left
  rewrite [union_def]
  exact Or.inr hC.right

Conclusion
"
Whew!
"
