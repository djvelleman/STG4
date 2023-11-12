import Game.Levels.Subset.L08contra

variable {U : Type}

World "Subset"
Level 9
Title "Complements"

Introduction
"
If `A` is a set of objects from the universe `U`, then the *complement* of `A`,
denoted `Aᶜ`, is the set of all objects in the universe `U` that are *not*
elements of `A`.  (You can enter the superscript `c` by typing `\\^c`.)

We'll need two new ideas in this level.  First, we'll need to use the definition of
\"complement\" in this proof.  To do that, we'll use a theorem that expresses the
definition.  The theorem `comp_def` says that for any object `x` and set `A`,
the statements `x ∈ Aᶜ` and `x ∉ A` are equivalent.  More precisely, if
you have `x : U` and `A : Set U`, then `comp_def x A` is a proof
of the statement `x ∈ Aᶜ ↔ x ∉ A`.

The theorem `x ∈ Aᶜ ↔ x ∉ A` tells us that if `x ∈ Aᶜ` occurs anywhere
in a proof, you can replace it with `x ∉ A`.  The tactic that does this is called
`rewrite`.
"

TacticDoc rewrite
"If the expression `t` is a proof of a statement of the form `P ↔ Q`, then the tactic
`rewrite [t]` will replace `P` anywhere that it occurs in the goal with `Q`.  If you want to
replace `Q` with `P`, use `rewrite [←t]`.  (Type `\\l` to enter the symbol `←`.)  To do the
replacement in an assumption `h`, use `rewrite [t] at h`.

The `rewrite` tactic can also be used with equations.  If `t` is a proof of an equation
`p = q`, then `rewrite [t]` will replace `p` with `q` wherever it appears, and `rewrite [←t]`
will replace `q` with `p`.

To do multiple replacements, one after another, put a list of proofs inside the brackets, like
this:  `rewrite [t1, t2]`."

NewTactic rewrite

DefinitionDoc comp as "ᶜ"
"If `A` is a of objects from the universe `U`, then `Aᶜ` is the complement of `A`; that is,
`Aᶜ` is the set of objects from `U` that are not elements of `A`."

NewDefinition comp

LemmaTab "Set Theory"

lemma comp_def (x : U) (A : Set U) : x ∈ Aᶜ ↔ x ∉ A := by rfl

LemmaDoc comp_def as "comp_def" in "Set Theory"
"If you have `x : U` and `A : Set U`, then `comp_def x A` is a proof of the statement
`x ∈ Aᶜ ↔ x ∉ A`."

NewLemma comp_def

/-- Suppose $A \subseteq B$ and $x ∈ B^c$.  Then $x \in A^c$. -/
Statement {A B : Set U} {x : U} (h1 : A ⊆ B) (h2 : x ∈ Bᶜ) : x ∈ Aᶜ := by
  Hint "To write out the meaning of the goal, use the tactic `rewrite [comp_def x A]`."
  rewrite [comp_def x A]
  Hint "The `rewrite` tactic is smart enough to figure out some things on its own.  If you
  had just written `rewrite [comp_def]`, then Lean would have figured out how to apply the
  theorem `comp_def` to get an equivalence that could be used to make a replacement in the goal.
  In other words, it would have figured out that the theorem `comp_def` had to be applied to
  `x` and `A`.

  Similarly, you can write `rewrite [comp_def] at h2` to write out the meaning of `h2`.  Lean
  will figure out that in this case, `comp_def` has to be applied to `x` and `B`."
  rewrite [comp_def] at h2
  Hint (hidden := true) "Now your goal is a negative statement, so try proof by contradiction."
  by_contra h3
  Hint (hidden := true) "This should remind you of the last level.  To get a contradiction,
  try to contradict `h2 : x ∉ B`."
  have h4 : x ∈ B := h1 h3
  exact h2 h4

Conclusion
"
We'll often use the `rewrite` tactic to write out definitions.
"
