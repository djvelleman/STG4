import Game.Levels.FamUnion

variable {U : Type}

World "FamCombo"
Level 1
Title "Complement of a family union"

Introduction
"
In this level you'll prove a generalization of the theorem `comp_union` that you proved
in Combination World.  That theorem was about the complement of a union of two sets; the
theorem in this level is about the complement of a union of a family of sets.

As in the case of `comp_union`, you have a choice about how to deal with the negations that
arise when you write out the meaning of complement.  You can use the `push_neg` tactic to
reexpress negative statements, or you can use proof by contradiction.
"

/-- For any family of sets $F$, $(\bigcup F)^c = \bigcap \{A \mid A^c \in F\}$. -/
Statement (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {A | Aᶜ ∈ F} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [set_builder_def] at h2
  rewrite [comp_def] at h1
  Branch
    by_contra h3
    Hint "Since `{h1}` is a negative statement, a good way to reach a contradiction
    would be to contradict it.  In other words, `{h1} _` would prove the goal `False` if you can
    fill in the blank with a proof of `{x} ∈ ⋃₀ F`.  That means the tactic `apply {h1}` will
    set your goal to be `{x} ∈ ⋃₀ F`."
  rewrite [fam_union_def] at h1
  push_neg at h1
  have h3 := h1 Sᶜ h2
  rewrite [comp_def] at h3
  push_neg at h3
  exact h3
  intro h1
  rewrite [fam_inter_def] at h1
  rewrite [comp_def]
  Branch
    by_contra h2
    rewrite [fam_union_def] at h2
    obtain ⟨S, hS⟩ := h2
    Hint (strict := true) "What set can you apply `{h1}` to?"
    have h2 := h1 Sᶜ
    Hint (strict := true) "To make use of `{h2}`, you'll need to assert `{S}ᶜ ∈ \{A | Aᶜ ∈ F}`.  If you don't see
    right away how to justify this assertion, you can just write `have {h2}a : {S}ᶜ ∈ \{A | Aᶜ ∈ F}`
    and Lean will set `{S}ᶜ ∈ \{A | Aᶜ ∈ F}` as your immediate goal.  Once you achieve that goal,
    Lean will add `{h2}a : {S}ᶜ ∈ \{A | Aᶜ ∈ F}` to your list of assumptions, and you can continue
    with the proof of your original goal.  For further details, click on `have` in the list of tactics
    on the right."
  rewrite [fam_union_def]
  push_neg
  intro S h2
  Hint (strict := true) "What set can you apply `{h1}` to?"
  have h3 := h1 Sᶜ
  Hint (strict := true) "To make use of `{h3}`, you'll need to assert `{S}ᶜ ∈ \{A | Aᶜ ∈ F}`.  If you don't see
  right away how to justify this assertion, you can just write `have {h3}a : {S}ᶜ ∈ \{A | Aᶜ ∈ F}`
  and Lean will set `{S}ᶜ ∈ \{A | Aᶜ ∈ F}` as your immediate goal.  Once you achieve that goal,
  Lean will add `{h3}a : {S}ᶜ ∈ \{A | Aᶜ ∈ F}` to your list of assumptions, and you can continue
  with the proof of your original goal.  For further details, click on `have` in the list of tactics
  on the right."
  have h3a : Sᶜ ∈ {A | Aᶜ ∈ F}
  rewrite [set_builder_def]
  rewrite [comp_comp]
  exact h2
  have h4 := h3 h3a
  rewrite [comp_def] at h4
  exact h4
