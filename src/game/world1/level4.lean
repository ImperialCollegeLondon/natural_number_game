/-
We just restarted Lean behind the scenes,
so let's re-import the natural numbers, but this time without
addition and multiplication.
-/

import mynat.definition -- import Peano's definition of the natural numbers {0,1,2,3,4,...}
namespace mynat -- hide

/- Axiom : zero_ne_succ (a : mynat) :
zero ≠ succ(a)
-/

/- Axiom : succ_inj (a b : mynat) :
succ(a) = succ(b) → a = b
-/

/- Axiom : one_eq_succ_zero
1 = succ(0)
-/
/-

# World 1 : Tutorial world

## Level 4: Peano's axioms.

The import above gives us the type `mynat` of natural numbers. But it
also gives us some other things, which we'll take a look at now:

  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after $n$".
  * The theorem `zero_ne_succ : ∀ a : mynat, zero ≠ succ(a)`.
    The upside-down A means "for all". So this is the axiom that zero isn't the 
    number after $a$, for any natural numbers $a$. The name means "zero not equal to succ".
  * The theorem `succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b`.
    This is the theorem that `succ` is injective, and the theorem name indicates this.
    A more mundane way of explaining it is: "if the number after $a$ is the number
    after $b$, then $a=b$."
  * The principle of mathematical induction.

These are the axioms isolated by Peano which uniquely characterise
the natural numbers. You don't have to learn the theorems off by heart -- they
are summarised in the "Theorem statements" drop-down box on the left (check
it now to see that they are there). However if you've not seen these things
before, I guess they might look intimidating, so let's just go through them briefly.
Firstly, notice
that they are all standard statements about the natural numbers $\{0,1,2,3,\ldots\}$.
The first axiom says that 0 is a natural number. The second says that there
is a `succ` function which eats a number and spits out the number after it,
so succ(0)=1, succ(1)=2 and so on. Then there are two theorems, both of
which are obvious. `zero_ne_succ` says that there's no number before 0,
and `succ_inj` says that if the
number after `a` equals the number after `b`, then `a = b`.

Peano's last axiom is the principle of mathematical induction. This is a deeper
fact. It says that if we have infinitely many true/false statements $P(0)$, $P(1)$,
$P(2)$ and so on, and if $P(0)$ is true, and if for every natural number $d$
we know that $P(d)$ implies $P(succ(d))$, then $P(n)$ must be true for every
natural number $n$. One can think of it as saying that every natural number
can be built by starting at 0 and then applying `succ` a finite number of times.

Peano's insights were firstly that these axioms completely characterise
the natural numbers, and secondly that these axioms alone can be used to build
a whole bunch of other structure on the natural numbers, for example
addition, multiplication and so on.

This game is all about seeing how far these axioms of Peano can take us.

The import also gives us usual numerical notation
0 and 1, where 0 is Peano's 0, and `1 = succ(0)`. It's sometimes useful to know that
`one_eq_succ_zero` is a proof of the theorem that `1 = succ(0)`.

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

on the line after `rw h,`. Don't forget blah blah blah.

**Important note** : the tactics `rw` and `exact` both expect
a proof afterwards (e.g. `rw h1`, `exact h2`). But `refl` is just `refl`.
Note also that the system sometimes drops brackets when they're not
necessary, and `succ b` just means `succ(b)`. 

You may be wondering whether we could have just substituted in the definition of `b`
and proved the goal that way. To do that, we would want to replace the right hand
side of `h` with the left hand side. You do this in Lean by writing `rw ← h`. You get the
left-arrow by typing `\l` and then a space. You can just edit your proof and try it. 

You may also be wondering why we keep writing `succ(b)` instead of `b+1`. This
is because we haven't defined addition yet! On the next level, the final level
of Tutorial World, we will introduce addition, and then
we'll be ready to enter Addition World.
-/

/- Lemma : no-side-bar
If $succ(a) = b$, then $succ(succ(a)) = succ(b)$.
-/
lemma example4 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) :=
begin [less_leaky]
  rw h,
  refl,



end

end mynat -- hide
