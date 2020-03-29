<h1><span style='color:#ff8c00'> Natural Number Game
</span></h1>

This is a game about the natural numbers, which are the numbers {0, 1, 2, 3, ...}. It is based on [this blog post](https://xenaproject.wordpress.com/2017/10/31/building-the-non-negative-integers-from-scratch/) but takes things a lot further.

The idea of the game is to teach you what actually goes into the *proofs* of all the statements about natural numbers which are presented to us as children and which we are told are "obvious". Examples of such statements are: `a + b = b + a`, or `a * (b + c) = a * b + a * c`.

If one uses a "geometric" and informal definition of addition, such as "`a + b` is the number of marbles you have, if you have `a` marbles in one hand and `b` in the other", then statements like `a + b = b + a` do become obvious. However such a definition of addition is not appropriate for a computer. Our job in this game is to convince a computer that statements such as `a + b = b + a` are not just "obvious", but actually have *proofs*.

In this game, we start with the natural numbers and the *principle of mathematical induction*, and induction is the main tool that we will be using. If you are already happy with the principle of mathematical induction then hopefully you will be able to make some progress playing this game, and it might even teach you more about what the principle is.

Computers are currently being taught mathematics by mathematicians, and this game will give you some idea about how one has to think about mathematics in order to teach it to a computer. Computer scientists would like to teach difficult modern research mathematics to a computer, but this is currently extremely hard to do because computers find it very hard to read mathematics written by humans, even with recent advances in machine learning and AI. This is a big stumbling block in training computers to become brilliant mathematicians. The natural numbers game teaches you a language which computers find it much easier to understand. The language we will be using is called Lean. Lean is a piece of free and open source software developed by Leonardo de Moura at Microsoft Research. 

# Playing the game

[Play here.](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/)

# Authors

Lean stuff: Kevin Buzzard. Find Kevin on [the Zulip Lean chat](https://leanprover.zulipchat.com) or on Twitter at [@XenaProject](https://twitter.com/XenaProject)

Computery stuff : [Mohammad Pedramfar](https://github.com/mpedramfar). See in particular [Lean game maker](https://github.com/mpedramfar/Lean-game-maker).

#naturalnumbergame
@XenaProject
