import Game.Levels.Comp

variable {U : Type}

World "Intersection"
Level 1
Title "And"

Introduction
"
To work with intersections, we'll need to understand the word \"and\".

If `P` and `Q` are statements, then `P ∧ Q` means \"P and Q\".  To enter the
symbol `∧`, type `\\and`.  For the statement `P ∧ Q` to be true, `P` and `Q` must
both be true.  If you have `h : P ∧ Q`--that is, `h` is a proof of
the statement `P ∧ Q`--then in Lean, `h.left` is a proof of `P` and `h.right` is
a proof of `Q`.  That should be all you need to know to solve this level.
"

DefinitionDoc and as "∧"
"`P ∧ Q` means \"P and Q\".  To enter the symbol `∧`, type `\\and`."

NewDefinition and

LemmaTab "Set Theory"

/-- Suppose $x \in A$ and $x \in B$.  Then $x \in A$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

Conclusion
"
Now we're ready to start proving theorems about intersections.
"
