import Game.Levels.Subset.L06subtrans  --It imports all previous levels.
/-!

# Subset world

This file defines Subset World. Like all worlds, this world
has a name, a title, an introduction, and most importantly
a finite set of levels (imported above). Each level has a
level number defined within it, and that's what determines
the order of the levels.
-/
World "Subset"
Title "Subset World"

Introduction
"Welcome to Subset World! In this world you will learn about sets and
subsets, and you will also learn the basics of proving theorems in Lean.

The elements of the sets in this world will come from a universe called `U`.
(Lean calls `U` a *Type*.)  To specify that an
object `x` belongs to the universe `U`, we write `x : U`.  To specify
that `A` is a set of objects from `U`, we write `A : Set U`.  To
say that `x` is an element of `A`, we write `x ∈ A`.  (You can enter
the symbol `∈` by typing `\\in`, followed by a space.)

You will prove theorems in this game by using tools called *tactics*.
The aim is to prove the theorem by applying tactics
in the right order.

Let's learn some basic tactics. Click on \"Start\" below
to get started.
"
