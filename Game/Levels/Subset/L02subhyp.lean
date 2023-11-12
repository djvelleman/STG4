import Game.Levels.Subset.L01exact

variable {U : Type}

World "Subset"
Level 2
Title "A subset hypothesis"

Introduction
"
If `A` and `B` are sets, then we say that `A` is a *subset* of `B` if
every element of `A` is also an element of `B`.  The notation `A ⊆ B` means
that `A` is a subset of `B`.  (To enter the symbol `⊆`, type `\\sub`,
followed by a space.)

If you have `h1 : A ⊆ B`, then `h1` is a proof that, if something is an element
of `A`, then it is also an element of `B`.  Thus, if you also have `h2 : x ∈ A`,
then you can apply `h1` to `h2` to conclude that `x ∈ B`.  To apply `h1` to `h2`,
you simply write `h1` followed by `h2`, with a space between them.  Thus, in
this situation, `h1 h2` is a proof of `x ∈ B`.

See if you can use this to complete this level.  If you need a hint, click on
\"Show more help!\".
"

DefinitionDoc sub as "⊆"
"`A ⊆ B` means that `A` is a subset of `B`.  To enter the symbol `⊆`,
type `\\sub`."

NewDefinition sub

/-- Suppose $A$ and $B$ are sets, $A \subseteq B$, and $x \in A$.
Then $x \in B$. -/
Statement (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  Hint (hidden := true) "Since `h1 h2` is a proof of `x ∈ B`, you can
  close the goal with `exact h1 h2`."
  exact h1 h2

Conclusion
"
This example is a better illustration of how the `exact` tactic is usually
used.  Often `exact` is followed by an expression that combines hypotheses
to prove the goal.  In later levels, we will see other ways in which
hypotheses can be combined to prove a goal.
"
