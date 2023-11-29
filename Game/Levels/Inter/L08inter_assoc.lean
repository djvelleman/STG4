import Game.Levels.Inter.L07inter_comm

variable {U : Type}

World "Intersection"
Level 8
Title "Intersection is associative"

Introduction
"
Our goal in this level is again an equation between sets.  In previous proofs of this kind,
we've started with the tactic `apply sub_antisymm`, and that would work here as well.
But we're going to try out an alternative: the tactic `ext`.  This tactic applies the principle
of *extensionality* for sets, which says that if
two sets have exactly the same elements, then they are equal.
"

/-
If your goal is `A = B`, where `A` and `B` are sets, and you use the tactic `ext x`, then Lean
will introduce a new arbitrary object `x` into the proof
and set the goal to be `x ∈ A ↔ x ∈ B`.  Proving that goal will show that
`A` and `B` have exactly the same elements, and by the principle of
extensionality, this shows that the sets are equal.

See if you can use the theorems and tactics you learned in previous levels to complete
this last theorem of Intersection World on your own.
-/

LemmaTab "Set Theory"

LemmaDoc inter_assoc as "inter_assoc" in "Set Theory"
"For any sets `A`, `B`, and `C`, `inter_assoc A B C` is a proof of the
statement `(A ∩ B) ∩ C = A ∩ (B ∩ C)`."

TacticDoc ext
"
If your goal is `A = B`, where `A` and `B` are sets, then the tactic `ext x` will introduce
a new arbitrary object `x` into the proof and set the goal to be `x ∈ A ↔ x ∈ B`.
"

NewTactic ext

/-- For any sets $A$, $B$, and $C$, $(A \cap B) \cap C = A \cap (B \cap C)$. -/
Statement inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  Hint "To start this proof, use the tactic `ext x`."
  ext x
  Hint "Notice that Lean has introduced the new object `x : U` into the proof, and
  your goal is now `x ∈ (A ∩ B) ∩ C ↔ x ∈ A ∩ (B ∩ C)`.  Proving this goal will show that
  `(A ∩ B) ∩ C` and `A ∩ (B ∩ C)` have exactly the same elements, and by the principle of
  extensionality, that will show that the sets are equal."
  Hint (hidden := true) "Since your goal is an \"if and only if\" statement, a good next step
  is `apply Iff.intro`."
  apply Iff.intro
  Hint (hidden := true) "Since your goal is an \"if-then\" statement, a good next step
  is `intro h1`."
  intro h1
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
  intro h1
  apply And.intro
  exact And.intro h1.left h1.right.left
  exact h1.right.right

NewLemma inter_assoc

Conclusion
"
Well done!  You're ready to move on to Union World.
"
