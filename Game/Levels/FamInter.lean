import Game.Levels.FamInter.L06eltwiseunion  --It imports all previous levels.
/-!

# FamInter world

-/
World "FamInter"
Title "Family Intersection World"

Introduction
"So far the elements of all of our sets have been objects in the universe `U`.  But
sets can contain other kinds of objects!  In the next two worlds, we will work with sets whose
elements are *sets of objects from `U`*.  We will call these *families of sets* from `U`.  To
indicate that `F` is a family of sets from `U`, we write `F : Set (Set U)`.

For example, suppose `U` contains the people in a certain club, and we want to form a committee
consisting of five members of the club.  The set of all possible committees is a family
of sets from `U`.  Each element of this family is a set containing five club members.

In this world we extend the idea of intersections to families of sets.  If `F` is a family of
sets from `U`, then the *intersection* of the family `F` is the set of all objects from `U`
that belong to every element of `F`.
"
