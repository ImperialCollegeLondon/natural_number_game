# How does it work?

## Overview

Kevin Buzzard wrote the levels in Lean. The definitions are hidden away from the end user: our target user is a
 mathematician who doesn't understand any type theory. We really wanted more than one proof on a page, but we
  couldn't work out how to make it work sensibly and accurately when the second proof depended on the first, so we
   gave in.

Mohammad Pedramfar used ideas from Patrick Massot's <a href="https://github.com/leanprover-community/format_lean"
 target="blank">Lean formatter</a>, and help from people like Bryan Gin-Ge Chen on the Lean chat, to make a 
 <a href="https://github.com/mpedramfar/Lean-game-maker" target="blank">lean game maker</a>. This tool can be used
  to make other Lean games. In practice the development of the natural number game and of the Lean game maker
   worked in parallel.

The Lean is standard Lean 3.4.2 but the tactic mode used is not quite Lean's tactic mode. Rob Lewis and Simon Hudon
 showed us how to make a modified tactic monad. If you take a look at a <a href="https://github.com/
 ImperialCollegeLondon/natural_number_game/blob/master/src/game/world10/level12.lean" target="blank">random level
 </a> you'll see that the begin/end block actually says `begin [nat_num_game] ... end`. The definition of this
  modified tactic monad is 
  <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/src/tactic/nat_num_game.lean"
   target="blank">here</a>. This means that we can slightly change the behaviour of some of Lean's tactics. For
    example <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/2bda565820d3711ed73440184dd2a184ef7f956c/src/tactic/modded.lean#L68" target="blank">
    here</a> we define a new tactic `induction'` and 
    <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/2bda565820d3711ed73440184dd2a184ef7f956c/src/tactic/nat_num_game.lean#L51" target="blank">
    here</a> we define the natural number game's induction tactic to be `induction'` and not `induction`. We also
     modify `cases`, `rw`, `symmetry` and `use`.

The main reasons we chose to modify `cases` and `induction` was the following. Lean's `rw` tactic works at the
level of syntactic equality, not definitonal equality. However Lean's `induction m` and `cases m` tactics insist
on replacing `m` with the exact constructurs used to define the type of `m`, so using Lean's induction will leave
you with goals containing `mynat.zero`, and rewrite lemmas referring to `0`, which is syntax sugar for
`has_zero.zero`. The terms `mynat.zero` and `(has_zero.zero : mynat)` are definitionally but not syntactically
equivalent and this makes rewrites fail, which is very confusing for beginner users. We fix this problem by using
a targetted `dsimp` to rewrite mynat.zero, mynat.le and mynat.lt to their canonical forms after Lean's actual
`induction` or `cases` tactic has run.

One might argue that beginner users will instead just get confused later when they download and start using normal
Lean on their computer -- but if they are using normal Lean on their computer and engaging with Lean beyond
the natural number game then we already won.

The other main change was that Lean's `rw` tries to close goals by `refl` when it has finish rewriting.
In practice this is an extremely useful feature. However for beginners just learning about equational
rewriting it can be very confusing when goals just start disappearing. The `rw` tactic in the `nat_num_game`
monad is simply Lean's usual `rw` with this extra feature removed. 

