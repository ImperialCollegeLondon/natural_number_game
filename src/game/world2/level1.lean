import mynat.definition -- Imports the natural numbers.
import mynat.add -- imports addition.
namespace mynat -- hide

-- World name : Addition world

/- Axiom : add_zero (a : mynat) :
a + 0 = a
-/

/- Axiom : add_succ (a b : mynat) :
a + succ(b) = succ(a + b)
-/

/- Tactic : induction

## Summary

if `n : mynat` is in our assumptions, then `induction n with d hd`
attempts to prove the goal by induction on `n`, with the inductive
assumption in the `succ` case being `hd`.

## Details

If you have a natural number `n : mynat` in your context
(above the `⊢`) then `induction n with d hd` turns your
goal into two goals, a base case with `n = 0` and
an inductive step where `hd` is a proof of the `n = d`
case and your goal is the `n = succ(d)` case.

### Example:
If this is our local context:
```
n : mynat
⊢ 2 * n = n + n
```

then

`induction n with d hd`

will give us two goals:

```
⊢ 2 * 0 = 0 + 0
```

and
```
d : mynat,
hd : 2 * d = d + d
⊢ 2 * succ d = succ d + succ d
```

-/


/- 
# Addition World. 

Welcome to Addition World. If you've done all four levels in tutorial world
and know about `rw` and `refl`, then you're in the right place. Here's
a reminder of the things you're now equipped with which we'll need in this world.

## Data:

  * a type called `mynat`
  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after `n`".
  * Usual numerical notation 0,1,2 etc (although 2 onwards will be of no use to us ;-) ).
  * Addition (with notation `a + b`).

## Theorems:

  * `add_zero (a : mynat) : a + 0 = a`
  * `add_succ (a b : mynat) : a + succ(b) = succ(a + b)`
  * The principle of mathematical induction. Use with `induction` (see below)
  

## Tactics:

  * `refl` -- proves goals of the form `X = X`
  * `rw h` -- if h is a proof of `A = B`, changes all A's in the goal to B's.
  * `induction n with d hd` -- we're going to learn this right now.

# Important thing: 

This is a *really* good time to check you understand about the box on the left with the drop down
menus. All the theorems and all the tactics above are documented there. You can find
all you need to know about what theorems you have collected in Theorem statements -> Addition world.
Have a click around and check that you can find statements of the theorems above, and explanations of
the tactics above. As we go through the game, these lists will grow. The box on the left
will prove invaluable as the number of theorems we prove gets bigger. On the other hand,
we only need to learn one more tactic to really start going places, so let's learn about
that tactic right now.

## Level 1: the `induction` tactic.

OK so let's see induction in action. We're going to prove

  `zero_add (n : mynat) : 0 + n = n`. 

That is: for all natural numbers $n$, $0+n=n$. Wait -- what is going on here?
Didn't we already prove that adding zero to $n$ gave us $n$?
No we didn't! We proved $n + 0 = n$ -- that proof was called `add_zero`. We're now
trying to establish `zero_add`, the proof that $0 + n = n$. But aren't these two theorems
the same? No they're not! It is *true* that `x + y = y + x`, but we haven't
*proved* it yet, and in fact we will need both `add_zero` and `zero_add` in order
to prove this. In fact `x + y = y + x` is the boss level for addition world,
and `induction` is the only other tactic you'll need to beat it.

Now `add_zero` is one of Peano's axioms, so we don't need to prove it, we already have it
(indeed, if you've opened the Addition World theorem statements on the left, you can even see it).
To prove `0 + n = n` we need to use induction on $n$. While we're here,
  note that `zero_add` is about zero add something, and `add_zero` is about something add zero.
  The names of the proofs tell you what the theorems are. Anyway, let's prove `0 + n = n`.

  Delete `sorry` and replace it with `induction n with d hd,`
and **don't forget the comma**. Hit enter, wait for Lean to finish thinking,
and let's see what we have.

When Lean has finished thinking, we see that we now have *two goals*! The
induction tactic has generated for us a base case with `n = 0` (the goal at the top)
and an inductive step (the goal underneath). The golden rule: **Tactics operate on the first goal** --
the goal at the top. So let's just worry about that top goal now, the base case `⊢ 0 + 0 = 0`.

Remember that `add_zero` (the proof we have already) is the proof of `x + 0 = x`
(for any $x$) so we can try

`rw add_zero,`

. What do you think the goal will
change to? Remember to just keep
focussing on the top goal, ignore the other one for now, it's not changing
and we're not working on it. You should be able to solve the top goal yourself
now with `refl`.

When you solved this base case goal, we are now be back down
to one goal -- the inductive step. Take a look at the
text below the lemma to see an explanation of this goal.
-/

/- Lemma
For all natural numbers $n$, we have
$$0 + n = n.$$
-/
lemma zero_add (n : mynat) : 0 + n = n :=
begin [less_leaky]
  induction n with d hd,
    rw add_zero,
    refl,
  rw add_succ,
  rw hd,
  refl

end

/-
We're in the successor case, and your top right box should look
something like this:

```
case mynat.succ
d : mynat,
hd : 0 + d = d
⊢ 0 + succ d = succ d
```

*Important:* make sure that you only have one goal at this point. You
should have proved `0 + 0 = 0` by now. Tactics only operate on the top goal.

The first line just reminds us we're doing the inductive step.
We have a fixed natural number `d`, and the inductive hypothesis `hd : 0 + d = d`
saying that we have a proof of `0 + d = d`.  
Our goal is to prove `0 + succ d = succ d`. In words, we're showing that
if the lemma is true for `d`, then it's also true for the number after `d`.
That's the inductive step. Once we've proved this inductive step, we will have proved
`zero_add` by the principle of mathematical induction.

To prove our goal, we need to use `add_succ`. We know that `add_succ 0 d`
is the result that `0 + succ d = succ (0 + d)`, so the first thing
we need to do is to replace the left hand side `0 + succ d` of our
goal with the right hand side. We do this with the `rw` command. You can write

`rw add_succ,`

(or even `rw add_succ 0 d,` if you want to give Lean all the inputs instead of making it
figure them out itself). Don't forget the comma though. Hit enter. The goal should change to

`⊢ succ (0 + d) = succ d`

Now remember our inductive hypothesis `hd : 0 + d = d`. We need
to rewrite this too! Type 

`rw hd,`

(don't forget the comma). The goal will now change to

`⊢ succ d = succ d`

This goal can be solved with the `refl` tactic. After you apply it,
Lean will inform you that there are no goals left. You are done!

## Now venture off on your own.

Those three tactics -- 

* `induction n with d hd,` 
* `rw h,`
* `refl,`

will get you quite a long way through this game. Using only these tactics
you can beat Addition World level 4 (the boss level of Addition World),
all of Multiplication World including the boss level `a * b = b * a`,
and even all of Power World including the fiendish final boss. This route will
give you a good grounding in these three basic tactics; after that, if you
are still interested, there are other worlds to master, where you can learn
more tactics.

But we're getting ahead of ourselves, you still have to beat the rest of Addition World. 
We're going to stop explaining stuff carefully now. If you get stuck or want
to know more about Lean (e.g. how to do much harder maths in Lean),
ask in `#new members` at
<a href="https://leanprover.zulipchat.com" target="blank">the Lean chat</a>
(login required, real name preferred). Kevin or Mohammad or one of the other
people there might be able to help.

Good luck! Click on "next level" to solve some levels on your own.

-/

end mynat -- hide