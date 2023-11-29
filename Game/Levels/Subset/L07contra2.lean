--Unused--contradiction introduced in Complement World.
--import Game.Levels.Subset.L06contra

variable {U : Type}

World "Subset"
Level 7
Title "More on proof by contradiction"

Introduction
"
Once again you have a goal that starts with `¬`, so proof by contradiction
seems like a good idea.
"

LemmaTab "Set Theory"

/-- Suppose $A \subseteq B$ and $\neg A \subseteq C$.  Then $\neg B \subseteq C$. -/
Statement {A B C : Set U} (h1 : A ⊆ B) (h2 : ¬A ⊆ C) : ¬B ⊆ C := by
  by_contra h3
  Hint "You already proved the theorem `sub_trans`, which says that if `A ⊆ B` and
  `B ⊆ C`, then `A ⊆ C`.  (Click on `sub_trans` in the list of theorems on the right
  to see what the theorem says.)  Since you now have `h1 : A ⊆ B` and `{h3} : B ⊆ C`, Lean
  will recognize `sub_trans h1 {h3}` as a proof of `A ⊆ C`.  Recall that you can
  enter the symbol `⊆` by typing `\\sub`."
  Hint (hidden := true) "Try `have h4 : A ⊆ C := sub_trans h1 {h3}`."
  have h4 : A ⊆ C := sub_trans h1 h3
  Hint "Now you have contradictory assumptions."
  Hint (hidden := true) "`h2` and `{h4}` give the required contradiction."
  exact h2 h4

Conclusion
"
Congratulations on completing Subset World!
"
