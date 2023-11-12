import Game.Levels.Inter

variable {U : Type}

World "Union"
Level 1
Title "Or"

Introduction
"
For working with unions, the important logical word is \"or\".

If `P` and `Q` are statements, then `P ∨ Q` means \"P or Q or both\".  To enter the
symbol `∨`, type `\\or`.  For the statement `P ∨ Q` to be true, either `P` or `Q` must
be true.  This gives us two ways to prove a statement of this form.  If you have
`h : P`, then `Or.inl h` can be used to prove `P ∨ Q`.  If you have `h : Q`, then
`Or.inr h` proves `P ∨ Q`.
"

DefinitionDoc or as "∨"
"`P ∨ Q` means \"P or Q or both\".  To enter the symbol `∨`, type `\\or`."

NewDefinition or

LemmaTab "Logic"

LemmaDoc Or.inl as "Or.inl" in "Logic"
"If you have `h : P`, then `Or.inl h` can be used as a proof of `P ∨ Q`, for
any statement `Q`."

LemmaDoc Or.inr as "Or.inr" in "Logic"
"If you have `h : Q`, then `Or.inr h` can be used as a proof of `P ∨ Q`, for
any statement `P`."

NewLemma Or.inl Or.inr

/-- Suppose $x \in A$, and $B$ is any set.  Then $x \in A ∨ x ∈ B$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

Conclusion
"
Now we're ready to start proving theorems about unions.
"
