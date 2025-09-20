import Game.Metadata

open Set

namespace STG4

variable {U : Type}

World "Intersection"
Level 1
Title "And"

Introduction
"
To work with intersections, we'll need to understand the word \"and\".

If `P` and `Q` are statements, then `P ∧ Q` means \"`P` and `Q`\".  To enter the
symbol `∧`, type `\\and`.  For the statement `P ∧ Q` to be true, `P` and `Q` must
both be true.  If you have `h : P ∧ Q`--that is, `h` is a proof of
the statement `P ∧ Q`--then in Lean, `h.left` is a proof of `P` and `h.right` is
a proof of `Q`.  That should be all you need to know to solve this level.
"

/-- `P ∧ Q` means "`P` and `Q`".  To enter the symbol `∧`, type `\and`.

### If your goal is `P ∧ Q`

If you have `hP : P` and `hQ : Q`, then `And.intro hP hQ` is a proof of `P ∧ Q`,
so `exact And.intro hP hQ` will close the goal.
If you don't yet have proofs of `P` and `Q`, then `apply And.intro` will set `P` and `Q`
as separate goals.  In this situation, the tactic `constructor` has the same effect as
`apply And.intro`.

### If you have an assumption `h : P ∧ Q`

Lean will recognize `h.left` as a proof of `P` and `h.right` as a proof of `Q`.
-/
DefinitionDoc and as "∧"

NewDefinition and

/-- Suppose $x \in A$ and $x \in B$.  Then $x \in A$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

Conclusion
"
Now we're ready to start proving theorems about intersections.
"
