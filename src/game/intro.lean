/-
# The Natural Number Game, version 1.1beta

## By Kevin Buzzard and Mohammad Pedramfar. 

# What is this game?

Welcome to the natural number game -- a part-book part-game which shows the power of induction.
Blue nodes on the graph are ones that you are ready to enter. Grey nodes you should stay away
from -- a grey node turns blue when *all* nodes above it are complete. Green nodes are completed.

In this game, you get own version of the natural numbers, called `mynat`, in a programming
language called Lean. Your version of the natural numbers satisfies something called
the principle of mathematical induction, and a couple
of other things too (Peano's axioms). Unfortunately, nobody has proved any theorems about these
natural numbers yet. For example, addition will be defined for you,
but nobody has proved that `x + y = y + x` yet. This is your job. You're going to
prove mathematical theorems using the Lean theorem prover. In other words, you're going to solve
levels in a computer game.

You're going to prove these theorems using *tactics*. The introductory world, Tutorial World,
will take you through some of these tactics. During your proofs, your "goal" (i.e. what you're
supposed to be proving) will be displayed with  a `⊢` symbol in front of it. If the top
right hand box reports "Theorem Proved!", you have closed all the goals in the level
and can move on to the next level in the world you're in. When you've finished a world,
hit "main menu" in the top left to get back here.

# What's new?

Pretty much all the <= levels of inequality world. I've <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/src/game/world10/level18a.lean" target="blank">written all the Lean code for "strictly less than"</a>  but am really busy with real life right now. In my dreams -- even/odd world. Feel free to fork and add your name to the list of authors. Instructions on how to build new worlds is on <a href="https://github.com/mpedramfar/Lean-game-maker" target="blank">Mohammad's Lean Game Maker site</a>. Any Imperial 1st year maths or JMC students -- do you want to help make <a href="https://github.com/ImperialCollegeLondon/real-number-game" target="blank">the real number game in Lean so you can prove $\operatorname{Sup}(X+Y)=\operatorname{Sup}(X)+\operatorname{Sup}(Y)$ *rigorously*? I've <a href="https://github.com/ImperialCollegeLondon/real-number-game/blob/a420eecef62209b729c910c2170d1dd27b74bc9f/world_plans/supinf.lean#L188" target="blank">done the Lean proof</a> and the only tactics you need to know are the ones in this game.

# Thanks

Special thanks to Rob Lewis for tactic hackery, Bryan Gin-Ge Chen for
javascript hackery, Patrick Massot for his
<a href="https://github.com/leanprover-community/format_lean" target="blank">Lean to html formatter</a>,
Sian Carey for Power World,
and, last but not least, all the people who fed back comments, including
the 2019-20 Imperial College 1st year maths beta tester students, Marie-Amélie Lawn,
Toby Gee, Joseph Myers, and all the people who have been in touch
via the <a href="https://leanprover.zulipchat.com/" target="blank">Lean Zulip chat</a>
 or the <a href="https://xenaproject.wordpress.com/" target="blank">Xena Project blog</a>
 or via <a href="https://twitter.com/XenaProject" target="blank">Twitter</a>.
The natural number game is brought to you by the Xena project, a project based at Imperial College London
whose aim is to get mathematics undergraduates using computer theorem provers.
Lean is a computer theorem prover being developed at Microsoft Research.

Prove a theorem. Write a function. <a href="https://twitter.com/XenaProject" target="blank">@XenaProject</a>.
-/
