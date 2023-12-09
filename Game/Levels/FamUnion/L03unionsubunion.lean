import Game.Levels.FamUnion.L02subunion

variable {U : Type}

World "FamUnion"
Level 3
Title "Union of larger family is larger"

Introduction
"
In this level we have two families of sets, `F` and `G`, with `F ⊆ G`.  In Family Intersection
World, you proved that in this situation, `⋂₀ G ⊆ ⋂₀ F`.  In this level, you'll prove that
with family unions, it works the other way: `⋃₀ F ⊆ ⋃₀ G`.

We'll need a new tactic for this proof.  An assumption of the form `h : ∃ x, P x` tells you that
an object with a certain property exists.  If you have such an assumption, then it is usually
helpful to introduce a name for such an object.  You can do this with the `obtain` tactic.  If
you write `obtain ⟨w, hw⟩ := h`, then Lean will introduce a new object `w` and a new assumption
`hw : P w`.  Thus, the object `w` is a witness for the existential assumption `h`.  Note that
in the `obtain` tactic, `w` and `hw` must be enclosed in angle brackets: `⟨ ⟩`.  You can
enter these by typing either `\\<` and `\\>` or `\\langle` and `\\rangle`.
"

TacticDoc obtain
"If you have an assumption `h : ∃ x, P x`, then the tactic `obtain ⟨w, hw⟩ := h` will
introduce a new object `w` and a new assumption `hw : P w` into the proof.  To enter the
angle brackets `⟨ ⟩`, type either `\\<` and `\\>` or `\\langle` and `\\rangle`."

NewTactic obtain

/-- Suppose $F$ and $G$ are families of sets and $F \subseteq G$.
Then $\bigcup F \subseteq \bigcup G$. -/
Statement (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x h2
  rewrite [fam_union_def]
  rewrite [fam_union_def] at h2
  Hint "The assumption `{h2}` is now an existential statement.  Thus, `obtain ⟨B, hB⟩ := {h2}`
  will introduce a new object `B` and a new assumption `hB : B ∈ F ∧ {x} ∈ B` into the proof.
  Once the witness `B` has been introduced, the assumption `{h2}` becomes redundant, so it is
  deleted."
  obtain ⟨B, hB⟩ := h2
  Hint (hidden := true) "Do you see why `{B}` is the value to use as a witness for `S` in the goal?
  Your next step can be either `apply Exists.intro {B}` or `use {B}`."
  apply Exists.intro B
  have h2 : B ∈ G := h1 hB.left
  exact And.intro h2 hB.right
