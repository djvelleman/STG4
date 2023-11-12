import Game.Levels.Subset.L04imp

variable {U : Type}

World "Subset"
Level 5
Title "If and only if"

Introduction
"
If `P` and `Q` are statements, then `P ↔ Q` means \"P if and only if Q\".
To enter the symbol `↔`, type `\\iff` (short for \"if and only if\").

The statement `P ↔ Q` means that both `P → Q` and `Q → P` are true.  Thus, you can prove
`P ↔ Q` by proving both `P → Q` and `Q → P`.  In fact, Lean knows a theorem called `Iff.intro`
that justifies this reasoning: if you have `h1 : P → Q` and `h2 : Q → P`, then `Iff.intro h1 h2` is
a proof of `P ↔ Q`.  You'll use that theorem, as well as the theorem `elt_imp_elt_of_sub` that
you proved in the last level, to complete this level.
"

DefinitionDoc iff as "↔"
"`P ↔ Q` means \"`P` if and only if `Q`\".  You can enter the symbol `↔` by typing `\\iff`."

NewDefinition iff

LemmaDoc Iff.intro as "Iff.intro" in "Logic"
"If you have `h1 : P → Q` and `h2 : Q → P`, then `Iff.intro h1 h2` is a proof of `P ↔ Q`."

NewLemma Iff.intro

LemmaTab "Logic"

/-- Suppose $A \subseteq B$, $B \subseteq A$, and $x$ is any object in the universe $U$.
Then $x \in A \leftrightarrow x \in B$. -/
Statement {A B : Set U} (h1 : A ⊆ B) (h2 : B ⊆ A) (x : U) : x ∈ A ↔ x ∈ B := by
  Hint (strict := true) "To prove the goal `x ∈ A ↔ x ∈ B`, you'll need to know both `x ∈ A → x ∈ B` and
  `x ∈ B → x ∈ A`.  To assert the first of this, write `have h3 : x ∈ A → x ∈ B := ...`.
  Of course, you'll have to fill in a justification for this statement.  (Recall that you can
  enter the symbols `∈` and `→` by typing `\\in` and `\\imp`, respectively.)"
  Hint (strict := true) (hidden := true) "You can use the theorem from the last level to justify this step.
  `elt_imp_elt_of_sub h1 x` is a proof of `x ∈ A → x ∈ B`."
  have h3 : x ∈ A → x ∈ B := elt_imp_elt_of_sub h1 x
  Hint (strict := true) "Do you see how you can also use `elt_imp_elt_of_sub` to justify
  `x ∈ B → x ∈ A`?"
  Hint (strict := true) (hidden := true) "`elt_imp_elt_of_sub h2 x` is a proof of `x ∈ B → x ∈ A`."
  have h4 : x ∈ B → x ∈ A := elt_imp_elt_of_sub h2 x
  Hint (strict := true) "Now you should be able to use the theorem `Iff.intro` to prove the goal."
  Hint (strict := true) (hidden := true) "`Iff.intro {h3} {h4}` is a proof of `x ∈ A ↔ x ∈ B`."
  exact Iff.intro h3 h4

Conclusion
"
This level illustrated the use of theorems.  You can find a list of theorems available for use
on the right.
"
