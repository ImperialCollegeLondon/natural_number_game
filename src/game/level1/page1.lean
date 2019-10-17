import mynat.definition -- Imports Peano's definition of the natural numbers.

namespace mynat -- hide
/- 
# The Natural Number Game (version v0.98 -- nearly there!)

Welcome to (a nearly-ready version of) the natural number game! Lean code by Kevin Buzzard, web stuff
by Mohammad Pedramfar. Special thanks to Rob Lewis for tactic hackery. And many many thanks to all the
Imperial 1st years who have given me feedback so far. We are going live with version 1.0
on 24th October, and any more feedback before then would be much appreciated.

## What is this game?

In this game, you get own version of the natural numbers, called `mynat`. Your version of the natural
numbers satisfies Peano's axioms. Unfortunately, nobody has proved any theorems about these natural
numbers yet. For example, addition will be defined for you, but nobody has proved that `x + y = y + x`
yet. This is your job.

You're going to prove these theorems using *tactics*. There are four tactics which you must know
before we start; these tactics are `refl`, `exact`, `rw` (which is short for "rewrite"), and
`induction`. This introductory level will take you through some of these tactics. During
your proofs, your "goal" (i.e. what you're supposed to be proving) will be displayed with 
a `⊢` symbol in front of it -- look for this symbol to find out what you're supposed to be
proving. 

## Tutorial level, page 1: `refl`

Let's start with the `refl` tactic. `refl` stands for "reflexivity", which is a fancy
way of saying that it will prove a goal of the form `x = x`.
Let's see it in action! Click the button below that says "Click here to prove !", then click
on the word `sorry` and read on.

-/
/- Lemma
For all natural numbers $x$, we have $x = x$.
-/
lemma example1 (x : mynat) : x = x :=
begin [less_leaky]
  refl
end
/-
When the system finishes being busy, In the box on the right you can see your goal -- the objective of this level. The goal
in this case is `x = x`. That's a pretty easy goal to prove -- you can just prove
it with the `refl` tactic. Delete `sorry` and change it to `refl,` (**don't forget the comma**).

If all is well, Lean should tell you that there are no goals left. You just did the first
level of the tutorial! Click on "next page" in the top left to go onto the second page of
tutorial world, where we'll learn about the `exact` tactic.
-/

end mynat -- hide 
