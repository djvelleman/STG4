import Game.Levels.Comp.L01contra

variable {U : Type}

World "Complement"
Level 2
Title "Complement subsets from subsets"

Introduction
"
There are some theorems that are pre-defined in this game, and you can use them to prove new
theorems.  In this level you'll use a pre-defined theorem that expresses the definition of
\"complement\".  The theorem `comp_def` says that for any object `x` and set `A`,
the statements `x ∈ Aᶜ` and `x ∉ A` are equivalent.  More precisely, if
you have `x : U` and `A : Set U`, then `comp_def x A` is a proof
of the statement `x ∈ Aᶜ ↔ x ∉ A`.  (The symbol `↔` means \"if and only if\", and you
can enter it by typing `\\iff`.  You can enter the superscript `c` in the notation for
the complement of a set by typing `\\^c`.)

You could think of the theorem `x ∈ Aᶜ ↔ x ∉ A` as saying that if `x ∈ Aᶜ` occurs anywhere
in a proof, you can replace it with `x ∉ A`.  There is a tactic called `rewrite` that can be
used to perform such replacements.  You'll get to try out the `rewrite` tactic in this level.
"

TacticDoc rewrite
"If the expression `t` is a proof of a statement of the form `P ↔ Q`, then the tactic
`rewrite [t]` will replace `P` anywhere that it occurs in the goal with `Q`.  If you want to
replace `Q` with `P`, use `rewrite [← t]`.  (Type `\\l` to enter the symbol `←`.)  To do the
replacement in an assumption `h`, use `rewrite [t] at h`.

The `rewrite` tactic can also be used with equations.  If `t` is a proof of an equation
`p = q`, then `rewrite [t]` will replace `p` with `q` wherever it appears, and `rewrite [←t]`
will replace `q` with `p`.

To do multiple replacements, one after another, put a list of proofs inside the brackets, like
this:  `rewrite [t1, t2]`."

NewTactic rewrite

DefinitionDoc comp as "ᶜ"
"If `A` is a of objects from the universe `U`, then `Aᶜ` is the complement of `A`; that is,
`Aᶜ` is the set of objects from `U` that are not elements of `A`.  You can enter the symbol `ᶜ`
by typing `\\^c`."

DefinitionDoc iff as "↔"
"`P ↔ Q` means \"P if and only if Q\".  You can enter the symbol `↔` by typing `\\iff`."

NewDefinition comp iff

LemmaTab "Set Theory"

lemma comp_def (x : U) (A : Set U) : x ∈ Aᶜ ↔ x ∉ A := by rfl

LemmaDoc comp_def as "comp_def" in "Set Theory"
"If you have `x : U` and `A : Set U`, then `comp_def x A` is a proof of the statement
`x ∈ Aᶜ ↔ x ∉ A`."

LemmaDoc comp_sub_of_sub as "comp_sub_of_sub" in "Set Theory"
"If you have `h : A ⊆ B`, then `comp_sub_of_sub h` is a proof of `Bᶜ ⊆ Aᶜ`."

/-- Suppose $A \subseteq B$.  Then $B^c \subseteq A^c$. -/
Statement comp_sub_of_sub {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  Hint "As usual, to prove a subset statement you need to introduce both a new object `x` and
  a new assumption `h2`.  You can do it in one step with `intro x h2`."
  intro x h2
  Hint "Now `comp_def {x} A` is a proof of the statement `{x} ∈ Aᶜ ↔ {x} ∉ A`, which tells us
  that we can reexpress the goal `{x} ∈ Aᶜ` as `{x} ∉ A`.  To do this reexpression,
  use the tactic `rewrite [comp_def x A]`."
  rewrite [comp_def x A]
  Hint "The `rewrite` tactic is smart enough to figure out some things on its own.  If you
  had just written `rewrite [comp_def]`, then Lean would have figured out how to apply the
  theorem `comp_def` to get an equivalence that could be used to make a replacement in the goal.
  In other words, it would have figured out that the theorem `comp_def` had to be applied to
  `{x}` and `A`.

  Similarly, you can write `rewrite [comp_def] at {h2}` to write out the meaning of `{h2}`.  Lean
  will figure out that in this case, `comp_def` has to be applied to `{x}` and `B`."
  rewrite [comp_def] at h2
  Hint (hidden := true) "Now your goal is a negative statement, so try proof by contradiction."
  by_contra h3
  Hint (hidden := true) "This should remind you of the last level.  To get a contradiction,
  try to contradict `{h2} : {x} ∉ B`."
  have h4 : x ∈ B := h1 h3
  exact h2 h4

NewLemma comp_def comp_sub_of_sub

Conclusion
"
The `rewrite` tactic is often useful for writing out definitions.  For more information about
how it works, click on `rewrite` in the list of tactics on the right.

You'll find the theorem you proved in this level listed as `comp_sub_of_sub` in the list of
theorems on the right.  This theorem will be useful in the last level of this world.
"
