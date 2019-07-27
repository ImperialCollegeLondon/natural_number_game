# natural_number_game
Building the natural numbers in Lean. 

To a mathematician, the fact that the natural numbers are a commutative
semiring is a theorem. It's a level in a game.

To the computer scientists, it is a definition.

The difference between their opinion and our opinion is a bunch
of data which it is hard for mathematicians to set up and understand
This repo just gives it to them, and just leaves the mathematicians
the job of proving the theorems.

See INSTRUCTIONS.txt for instructions for Lean-competent people.
**BETTER INSTRUCTIONS NEED TO BE WRITTEN**

### CoCalc

You can play this game online on CoCalc. Ask Kevin for information.

### Installation instructions

If you want to play offline then you'll have to install the game.

Assuming you have installed Lean and the supporting tools, for example
by following the installation instructions at https://github.com/leanprover-community/mathlib,
the installation process for this project is:

```
git clone git@github.com:ImperialCollegeLondon/natural_number_game.git
cd natural_number_game
leanpkg configure
update-mathlib
```

### Playing the game

At the minute, the only way to play it is to
(1) read `instructions.txt`
(2) edit the files `world1_addition.lean` etc

