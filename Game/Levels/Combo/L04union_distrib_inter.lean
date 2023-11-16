import Game.Levels.Combo.L03inter_distrib_union

variable {U : Type}

World "Combination"
Level 4
Title "Union distributes over intersection"

Introduction
"
This is different from the previous theorem--the roles of union and intersection have
been swapped.  But if you made it through the last one, you can do this one too!
"

LemmaTab "Set Theory"

LemmaDoc union_distrib_over_inter as "union_distrib_over_inter" in "Set Theory"
"For any sets `A`, `B`, and `C`, `union_distrib_over_inter A B C` is a proof of the
statement `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`."

/-- For any sets $A$, $B$, and $C$, $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$. -/
Statement union_distrib_over_inter (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply sub_antisymm
  intro x h
  rewrite [inter_def]
  rewrite [union_def] at h
  cases' h with hA hBC
  apply And.intro
  rewrite [union_def]
  exact Or.inl hA
  rewrite [union_def]
  exact Or.inl hA
  rewrite [inter_def] at hBC
  apply And.intro
  exact Or.inr hBC.left
  exact Or.inr hBC.right
  intro x h
  rewrite [inter_def] at h
  rewrite [union_def]
  have hAB : x ∈ A ∪ B := h.left
  have hAC : x ∈ A ∪ C := h.right
  rewrite [union_def] at hAB
  cases' hAB with hA hB
  exact Or.inl hA
  rewrite [union_def] at hAC
  cases' hAC with hA hC
  exact Or.inl hA
  apply Or.inr
  rewrite [inter_def]
  exact And.intro hB hC

NewLemma union_distrib_over_inter

Conclusion
"
To finish off Union World, we'll do one more tricky theorem.
"
