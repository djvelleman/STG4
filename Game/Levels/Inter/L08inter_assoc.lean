import Game.Levels.Inter.L07inter_comm

variable {U : Type}

World "Intersection"
Level 8
Title "Intersection is associative"

Introduction
"
See if you can use the theorems and tactics you learned in previous levels to complete
this last theorem of Intersection World on your own.
"

LemmaTab "Set Theory"

LemmaDoc inter_assoc as "inter_assoc" in "Set Theory"
"For any sets `A`, `B`, and `C`, `inter_assoc A B C` is a proof of the
statement `(A ∩ B) ∩ C = A ∩ (B ∩ C)`."

/-- For any sets $A$, $B$, and $C$, $(A \cap B) \cap C = A \cap (B \cap C)$. -/
Statement inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply sub_antisymm
  intro x h1
  rewrite [inter_def]
  rewrite [inter_def] at h1
  Hint (strict := true) (hidden := true) "If you're stuck at this point,
  it may help you see how to proceed if you separate
  out the first half of `{h1}` as a separate assumption.
  You can do this with `have hAB : {x} ∈ A ∩ B := {h1}.left`."
  have h2 : x ∈ A ∩ B := h1.left
  rewrite [inter_def] at h2
  apply And.intro
  exact h2.left
  exact And.intro h2.right h1.right
  intro x h1
  apply And.intro
  exact And.intro h1.left h1.right.left
  exact h1.right.right

NewLemma inter_assoc

Conclusion
"
Well done!  You're ready to move on to Union World.
"
