import Game.Metadata
import Game.Levels.Comp

open Set

namespace STG4

variable {U : Type}

World "Combination"
Level 1
Title "Complement of a union"

Introduction
"
There is more than one way to do the proof in this level.  Since the proof involves complements of
sets, negative statements will arise in the course of the proof.  This suggests two possible techniques.
You may be able to use the `push_neg` tactic to reexpress some negative statements as equivalent
positive statements.  And you may find proof by contradiction useful.
"

TheoremTab "ᶜ"

/-- For any sets `A` and `B`, `compl_union A B` is a proof of the
statement `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`.  In Mathlib, the name of this theorem is `Set.compl_union`. -/
TheoremDoc STG4.compl_union as "compl_union" in "ᶜ"

/-- For any sets $A$ and $B$, $(A \cup B)^c = A^c \cap B^c$. -/
Statement compl_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  rewrite [mem_compl_iff, mem_union]
  rewrite [mem_inter_iff, mem_compl_iff, mem_compl_iff]
  apply Iff.intro
  intro h
  push_neg at h
  exact h
  intro h
  push_neg
  exact h
