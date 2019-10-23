import mynat.definition -- hide
namespace mynat -- hide

/-

# World 1 : Tutorial world

## level 4: more rewriting.

Way back on page 1 we imported a file called `mynat.definition`.
This gave us the type `mynat` of natural numbers. But it
also gave us some other things:

  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after n".
  * The theorem `zero_ne_succ : ∀ a : mynat, zero ≠ succ(a)`.
    This is the axiom that zero isn't a successor. The name means "zero not equal to succ".
  * The theorem `succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b`.
    This is the theorem that `succ` is injective, and the theorem name indicates this.
  * The principle of mathematical induction.

These are the five axioms isolated by Peano, which uniquely characterise
the natural numbers. If you've not seen them before, I guess they might
look intimidating, so let's just go through them briefly. They are all
obvious statements about the natural numbers {0,1,2,3,...}. The first axiom
says that 0 is a natural number. The `succ` function eats a number
and spits out the number after it, so succ(0)=1, succ(1)=2 and so on. 
The theorem `zero_ne_succ` makes sure that there's no number before 0,
and `succ_inj` ensures that numbers go on forever.
And the principle of mathematical induction
tells us that every natural number can be built by starting at 0 and
then applying `succ` some finite number of times.

Peano's insights were firstly that these axioms completely characterise
the natural numbers, and secondly that these axioms alone can be used to build
a whole bunch of other structure on the natural numbers, for example
addition, multiplication and so on. 
This game is all about seeing how far these
axioms of Peano will take us.

The import also gives us usual numerical notation
0,1,2,3,4,5 etc, with `1 = succ(0)`, `2=succ(1)` and so on.
`one_eq_succ_zero` is a proof of the theorem that `1 = succ(0)`.

Let's practice our use of the `rw` tactic in the following example.
Our hypothesis `h` is a proof that `b = succ(a)` and we want to prove that
`succ(b)=succ(succ(a))`. In words, we're going to prove that if
`b` is the number after `a` then `succ(b)` is the number after `succ(a)`. 
Now `h` gives us a formula for `b` and we just want to substitute in.
*This is exactly what the `rw` tactic does*.
Before you delete the sorry and write

`rw h,`

and hit enter whilst not forgetting the comma, try and figure out
what the goal will become. The answer: it will become `succ(succ(a))=succ(succ(a))`,
and that goal is of the form `X = X` (if the goal goes onto a
second line, resize the top right window -- make it wider by dragging
its left hand edge). You can prove this new goal with

`refl,`

on the line after `rw h`,. Don't forget blah blah blah.

**Important note** : the tactics `rw` and `exact` both expect
a proof afterwards (e.g. `rw h1,`, `exact h2,`), But `refl,` is just `refl,`.
Note also that the system sometimes drops brackets when they're not
necessary, and `succ b` just means `succ(b)`. 

On the next level, the final level of Tutorial World, we will introduce
addition, and when we've solved it we'll be ready to enter Addition World.
-/

/- Lemma : no-side-bar
If `b = succ(a)`, then `succ(b) = succ(succ(a))`.
-/
lemma example4 (a b : mynat) (h : b = succ a) : succ b = succ (succ a) :=
begin [less_leaky]
  rw h,
  refl,



end

end mynat -- hide
