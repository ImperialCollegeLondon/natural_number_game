/-
# The Natural Number Game, version 1.2rc2

## By Kevin Buzzard and Mohammad Pedramfar. 

Works in Chrome. Usually works in other browsers. If you see "Lean is busy" and it hasn't gone
away after about 20 seconds, try Chrome. Recent Firefox works fine. Safari
13.0.3 has been reported not to work, but Safari 13.1 apparently works fine.
Cookies need to be enabled to make Lean work in your browser.

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

Lots of typo fixes. Thank you, all the people who made PR's and opened issues. This is Kevin's first ever open source project and it is an amazing experience.

# What's to come?

Still haven't ported the <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/src/game/world10/level18a.lean" target="blank">
less-than worlds</a>.

# Hey, real Lean works slightly differently to this Lean. What is going on?

Here is a <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/docs/technical.md" target="blank">
technical explanation</a> of how it all works.

# I love these levels! Where can I get more of this stuff?

Read about <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/WHATS_NEXT.md" target="blank">what's next</a> here.

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
