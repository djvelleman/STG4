import Game.Levels.Inter.L05subint

variable {U : Type}

World "Intersection"
Level 6
Title "Intersection subset of swap"

Introduction
"
In the next level we're going to prove that intersection is commutative; that is,
`A ∩ B = B ∩ A`.  As a warm-up, in this level we prove `A ∩ B ⊆ B ∩ A`.
"

LemmaTab "Set Theory"

LemmaDoc inter_sub_swap as "inter_sub_swap" in "Set Theory"
"For any sets `A` and `B`, `inter_sub_swap A B` is a proof of
`A ∩ B ⊆ B ∩ A`."

/-- For any sets $A$ and $B$, $A \cap B \subseteq B \cap A$. -/
Statement inter_sub_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x h
  Hint (hidden := true) "It will help you see how to proceed if you
  write out the definition of intersection in both the assumption {h} and the goal."
  rewrite [inter_def]
  rewrite [inter_def] at h
  Hint (hidden := true) "Now `And.intro {h}.right {h}.left` proves the goal."
  exact And.intro h.right h.left

NewLemma inter_sub_swap

Conclusion
"
We have given this theorem the name `inter_sub_swap`.  Thus, from now on, for
any sets `A` and `B`, `inter_sub_swap A B` is a proof of `A ∩ B ⊆ B ∩ A`.
"
