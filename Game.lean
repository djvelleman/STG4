-- Here's the import to make Lean know about things called `Game`s
--import GameServer.Commands  --unnecessary because imported by first level

-- Here are the imports defining many worlds for the game `Game`.
-- Each world consists of a finite number of levels, and levels
-- are numbered 1,2,3,4... inside the level files.
--import Game.Levels.Subset   --only need to import last level
--import Game.Levels.Comp
--import Game.Levels.Inter
--import Game.Levels.Union
import Game.Levels.FamCombo

-- Here's what we'll put on the title screen
Title "Set Theory Game"
Introduction
"
# Welcome to the Set Theory Game
#### An introduction to mathematical proof.

In this game, you will solve a sequence of levels by proving theorems.  The game
is based on an interactive theorem prover called *Lean*.

The theorems in this game will be about sets.
A *set* is a collection of objects; the objects in the collection are
called *elements* of the set.  For example, the set of planets in our
solar system has eight elements:
Mercury, Venus, Earth, Mars, Jupiter, Saturn, Uranus, and Neptune.

# Read this.

Learning how to use an interactive theorem prover takes time.
You will get the most out of this game if you
read the help texts like this one.

To start, click on \"Subset World\".

## More

Open \"Game Info\" in the \"≡\" menu on the top right for resources,
links, and ways to interact with the Lean community.
"

Info "
*Game version: 4.1*

## Progress saving

The game stores your progress in your local browser storage.
If you delete it, your progress will be lost!

Warning: In most browsers, deleting cookies will also clear the local storage
(or \"local site data\"). Make sure to download your game progress first!

## Credits

* **Creator:** Daniel J. Velleman; based on the Natural Numbers Game, by Kevin Buzzard
* **Game Engine:** Alexander Bentkamp, Jon Eugster, Patrick Massot

## Resources

* The [Lean Zulip chat](https://leanprover.zulipchat.com/) forum

## Problems?

Please ask any questions about this game in the
[Lean Zulip chat](https://leanprover.zulipchat.com/) forum, for example in
the stream \"New Members\". The community will happily help. Note that
the Lean Zulip chat is a professional research forum.
Please use your full real name there, stay on topic, and be nice. If you're
looking for somewhere less formal (e.g. you want to post set theory
game memes) then head on over to the [Lean Discord](https://discord.gg/WZ9bs9UCvx).

Alternatively, if you experience issues / bugs you can also open github issues:

* For issues with the game engine, please open an
[issue at the lean4game repo](https://github.com/leanprover-community/lean4game/issues).
* For issues about the game's content, please open an
[issue at the STG repo](https://github.com/djvelleman/STG4/issues).
"

-- Here we could add additional connections between the worlds
-- The game automatically computes connections between worlds based on introduced
-- tactics and theorems, but for example it cannot detect introduced definitions

-- Dependency Implication → Power -- `Power` uses `≠` which is introduced in `Implication`

-- Future plan for the game:
-- Dependency AdvAddition → AdvMultiplication → Inequality → Prime → Hard
-- Dependency Multiplication → AdvMultiplication
-- Dependency AdvAddition → EvenOdd → Inequality → StrongInduction

Dependency Intersection → Union
Dependency FamInter → FamUnion

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "A game about set theory."
CaptionLong "In this game you will learn the basics of theorem proving in Lean by proving
theorems about unions, intersections, and complements of sets."

MakeGame
