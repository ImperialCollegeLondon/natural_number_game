/-
We just restarted Lean behind the scenes,
so let's re-import the natural numbers, but this time without
addition and multiplication.
-/

import mynat.definition -- import Peano's definition of the natural numbers {0,1,2,3,4,...}
namespace mynat -- hide

/-

# Tutorial world

## Level 3: Peano's axioms.

The import above gives us the type `mynat` of natural numbers. But it
also gives us some other things, which we'll take a look at now:

  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after $n$".
  * The principle of mathematical induction.

These axioms are essentially the axioms isolated by Peano which uniquely characterise
the natural numbers (we also need recursion, but we can ignore it for now).
The first axiom says that $0$ is a natural number. The second says that there
is a `succ` function which eats a number and spits out the number after it,
so $\operatorname{succ}(0)=1$, $\operatorname{succ}(1)=2$ and so on.

Peano's last axiom is the principle of mathematical induction. This is a deeper
fact. It says that if we have infinitely many true/false statements $P(0)$, $P(1)$,
$P(2)$ and so on, and if $P(0)$ is true, and if for every natural number $d$
we know that $P(d)$ implies $P(\operatorname{succ}(d))$, then $P(n)$ must be true for every
natural number $n$. It's like saying that if you have a long line of dominoes, and if
you knock the first one down, and if you know that if a domino falls down then the one
after it will fall down too, then you can deduce that all the dominos will fall down.
One can also think of it as saying that every natural number
can be built by starting at `0` and then applying `succ` a finite number of times.

Peano's insights were firstly that these axioms completely characterise
the natural numbers, and secondly that these axioms alone can be used to build
a whole bunch of other structure on the natural numbers, for example
addition, multiplication and so on.

This game is all about seeing how far these axioms of Peano can take us.

Let's practice our use of the `rw` tactic in the following example.
Our hypothesis `h` is a proof that `succ(a) = b` and we want to prove that
`succ(succ(a))=succ(b)`. In words, we're going to prove that if
`b` is the number after `a` then `succ(b)` is the number after `succ(a)`. 
Now here's a tricky question. If our goal is `⊢ succ (succ a) = succ b`,
and our hypothesis is `h : succ a = b`, then what will the goal change
to when we type

`rw h,`

and hit enter whilst not forgetting the comma? Remember that `rw h` will
look for the *left* hand side of `h` in the goal, and will replace it with
the *right* hand side. Try and figure out how the goal will change, and
then try it.

The answer: Lean changed `succ a` into `b`, so the goal became `succ b = succ b`.
That goal is of the form `X = X`, so you can prove this new goal with

`refl,`

on the line after `rw h,`. Don't forget the commas!

**Important note** : the tactic `rw` expects
a proof afterwards (e.g. `rw h1`). But `refl` is just `refl`.
Note also that the system sometimes drops brackets when they're not
necessary, and `succ b` just means `succ(b)`. 

You may be wondering whether we could have just substituted in the definition of `b`
and proved the goal that way. To do that, we would want to replace the right hand
side of `h` with the left hand side. You do this in Lean by writing `rw ← h`. You get the
left-arrow by typing `\l` and then a space; note that this is a small letter L,
not a number 1. You can just edit your proof and try it. 

You may also be wondering why we keep writing `succ(b)` instead of `b+1`. This
is because we haven't defined addition yet! On the next level, the final level
of Tutorial World, we will introduce addition, and then
we'll be ready to enter Addition World.
-/

/- Lemma : no-side-bar
If $\operatorname{succ}(a) = b$, then
$$\operatorname{succ}(\operatorname{succ}(a)) = \operatorname{succ}(b).$$
-/
lemma example3 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) :=
begin [nat_num_game]
  rw h,
  refl,



end

end mynat -- hide
