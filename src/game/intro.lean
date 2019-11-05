/-
# The Natural Number Game, version 1.08beta [see "what's new" below]

[will be ready to go after some updates to the engine which generates the web pages]

## By Kevin Buzzard and Mohammad Pedramfar. 

Special thanks to Rob Lewis for tactic hackery, Sian Carey for power world (world 4),
and, last but not least, all the people who fed back comments, including
the 2019-20 Imperial College 1st year maths beta tester students, Marie-Amélie Lawn,
Toby Gee, Joseph Myers, and all the people who have been in touch
via the <a href="https://leanprover.zulipchat.com/" target="blank">Lean Zulip chat</a>
 or the <a href="https://xenaproject.wordpress.com/" target="blank">Xena Project blog</a>
 or via <a href="https://twitter.com/home" target="blank">Twitter</a>.
The natural number game is brought to you by the Xena project, a project based at Imperial College London
whose aim is to get mathematics undergraduates using computer theorem provers.
Lean is a computer theorem prover being developed at Microsoft Research.

# What is this game?

Welcome to the natural number game -- a game which shows the power of induction.


In this game, you get own version of the natural numbers, called `mynat`, in a programming
language called Lean. Your version of the natural numbers satisfies something called
the principle of mathematical induction, and a couple
of other things too (Peano's axioms). Unfortunately, nobody has proved any theorems about these
natural numbers yet. For example, addition will be defined for you,
but nobody has proved that `x + y = y + x` yet. This is your job. You're going to
prove mathematical theorems using the Lean theorem prover. In other words, you're going to solve
levels in a computer game.

You're going to prove these theorems using *tactics*. This introductory world, Tutorial World,
will take you through some of these tactics. During your proofs, your "goal" (i.e. what you're
supposed to be proving) will be displayed with  a `⊢` symbol in front of it. If the top
right hand box reports "Theorem Proved!", you have closed all the goals in the level
and can move on to the next level in the world you're in. 
-/