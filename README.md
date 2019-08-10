<h1><span style='color:#ff8c00'> Natural Number Game
</span></h1>

Warning: this is version 0.0.1beta.

This is a game about the natural numbers, which are the numbers {0, 1, 2, 3, ...}.

The idea of the game is to teach you what actually goes into the *proofs* of all the statements about natural numbers which are presented to us as children and which we are told are "obvious". Examples of such statements are: `a + b = b + a`, or `a * (b + c) = a * b + a * c`.

If one uses a "geometric" and informal definition of addition, such as "`a + b` is the number of marbles you have, if you have `a` marbles in one hand and `b` in the other", then statements like `a + b = b + a` do become obvious. However such a definition of addition is not appropriate for a computer. Our job in this game is to convince a computer that statements such as `a + b = b + a` are not just "obvious", but actually have *proofs*.

In this game, we start with the natural numbers and the *principle of mathematical induction*, and induction is the main tool that we will be using. If you are already happy with the principle of mathematical induction then hopefully you will be able to make some progress playing this game, and it might even teach you more about what the principle is.

Computers are currently being taught mathematics by mathematicians, and this game will give you some idea about how one has to think about mathematics in order to teach it to a computer. Computer scientists would like to teach difficult modern research mathematics to a computer, but this is currently extremely hard to do because computers find it very hard to read mathematics written by humans, even with recent advances in machine learning and AI. This is a big stumbling block in training computers to become brilliant mathematicians. The natural numbers game teaches you a language which computers find it much easier to understand. The language we will be using is called Lean. Lean is a piece of free and open source software developed by Leonardo de Moura at Microsoft Research. 

# Getting the game working.

This game is still very much in beta mode. In the future there will be a much easier interface to playing the game via a web browser without installing anything, but until that point, to play the game there are really only two options.

## Option 1: playing the game on your own computer.

First, you will have to [install Lean, its maths library mathlib, and Visual Studio Code on your computer](https://github.com/leanprover-community/mathlib#installation).

Once you have done this, you can clone and compile this repository with the following code:
```
git clone git@github.com:ImperialCollegeLondon/natural_number_game.git
cd natural_number_game
leanpkg configure
update-mathlib
```

Next, in VS Code, select File -> Open Folder and open the `natural number game` directory.

Finally, open src/my_solutions/world1_addition.lean and now you're playing the game.

## Option 2: playing the game on CoCalc.com

To be written.

# Playing the game

Read the [instructions on how to play the game](INSTRUCTIONS.md).

# Author

Lean stuff: Kevin Buzzard @XenaProject 
Computery stuff : Maybe Kevin Kappelmann, maybe Mohammad Pedramfar

#naturalnumbergame
