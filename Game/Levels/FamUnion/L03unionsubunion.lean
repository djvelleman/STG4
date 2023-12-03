import Game.Levels.FamUnion.L02subunion

variable {U : Type}

World "FamUnion"
Level 3
Title "Union of Larger Family is Larger"

Introduction
"
In this level we have two families of sets, `F` and `G`, with `F ⊆ G`.  In Family Intersection
World, you proved that in this situation, `⋂₀ G ⊆ ⋂₀ F`.  In this level, you'll prove that
with family unions, it works the other way: `⋃₀ F ⊆ ⋃₀ G`.
"

/-- Suppose $F$ and $G$ are families of sets and $F \subseteq G$.
Then $\bigcup F \subseteq \bigcup G$. -/
Statement (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x h2
  rewrite [fam_union_def]
  rewrite [fam_union_def] at h2
  Hint "The assumption {h2} says that there some set `S` such that `S ∈ F ∧ {x} ∈ S` is true.
  It would help to introduce a name for such a set.  You can do this with the `cases'` tactic.
  If you write `cases' {h2} with B hB`, then Lean will introduce a new object `B` and a new
  assumption `hB : B ∈ F ∧ {x} ∈ B`.  (It seems a little odd to use the `cases'` tactic
  in this situation, because this is not an example of proof by cases.  Nevertheless, the
  `cases'` tactic does what we need.)"
  cases' h2 with B hB
  Hint (hidden := true) "Do you see why `B` is the value to use for `S` in the goal?  Your next
  step can be either `apply Exists.intro B` or `use B`."
  apply Exists.intro B
  have h2 : B ∈ G := h1 hB.left
  exact And.intro h2 hB.right
