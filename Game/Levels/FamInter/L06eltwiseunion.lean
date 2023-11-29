import Game.Levels.FamInter.L05subinter

variable {U : Type}

World "FamInter"
Level 6
Title "Intersection of a Family of Unions"

Introduction
"
In this level you'll use a new kind of proof by cases.  For any statement `P`, the
tactic `by_cases h : P` will break the proof into two cases.  In the first case, the new
assumption `h : P` is added to the list of assumptions, and in second the new
assumption `h : ¬P` is added.  Since `P` must be either true or false, these two cases cover
all possibilities.
"

TacticDoc by_cases
"
The tactic `by_cases h : P` breaks the proof into two cases.  In the first case, the
assumption `h : P` is added to the list of assumptions, and in the second case, the
assumption `h : ¬P` is added.
"

NewTactic by_cases

/-- Suppose $A$ is a set, $F$ and $G$ are families of sets, and for every set $S$ in $F$,
$A \cup S \in G$.  Then $\bigcap G \subseteq A \cup (\bigcap F)$.-/
Statement (A : Set U) (F G : Set (Set U)) (h1 : ∀ S ∈ F, A ∪ S ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro x h2
  Hint "Writing out the meaning of the goal will make the proof easier to understand."
  rewrite [union_def]
  Hint (strict := true) "If `{x} ∈ A`, then the goal is easy to prove.  This suggests breaking the proof into
  cases depending on whether or not `{x} ∈ A`.  You can do this with the tactic
  `by_cases h3 : {x} ∈ A`."
  by_cases h3 : x ∈ A
  Hint "The first case is the easy one."
  exact Or.inl h3
  Hint "For the second case, which half of the goal do you think you should try to prove?
  You can use `apply Or.inl` or `apply Or.inr` (or the equivalent tactics `left` or `right`)
  to specify what goal you're going to prove."
  apply Or.inr
  rewrite [fam_inter_def]
  intro S h4
  Hint (strict := true) (hidden := true) "Now use `h1`."
  have h5 : A ∪ S ∈ G := h1 S h4
  Hint (strict := true) (hidden := true) "You haven't used `h2` yet.  If you don't see how to use it,
  write out its definition."
  rewrite [fam_inter_def] at h2
  Hint (strict := true) (hidden := true) "Note that you can apply `h2` to `(A ∪ {S})`."
  have h6 : x ∈ A ∪ S := h2 (A ∪ S) h5
  rewrite [union_def] at h6
  cases' h6 with hA hS
  by_contra h6
  exact h3 hA
  exact hS

Conclusion
"

"
