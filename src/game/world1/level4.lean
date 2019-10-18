import mynat.definition -- hide
namespace mynat -- hide

/-

## Tutorial world, level 4: more rewriting.

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
the natural numbers. This game is all about seeing how far these
axioms will take us.

The import also offers us usual numerical notation
0,1,2,3,4,5 etc, with `1 = succ(0)`, `2=succ(1)` and so on.

Let's practice our use of the `rw` tactic in the following example.
Our hypothesis is that `a = succ(b)` and we want to prove that
`succ(a)=succ(succ(b))`. We know what `a` is so we just want
to substitute in! This is exactly what the `rw` tactic does.
Before you delete the sorry and write

`rw h,`

and hit enter whilst not forgetting the comma, try and guess
what the goal will become. If you guessed right, you will know
that the goal is of the form `X = X` (if the goal goes onto a
second line, resize the window and make it wider by dragging
the left hand edge). You can prove this goal with

`refl,`

**Important note** : the tactics `rw` and `exact` both expect
a proof afterwards (e.g. `rw h1,`, `exact h2,`), But `refl,` is just `refl,`.
Note also that the system sometimes drops brackets when they're not
necessary, and `succ b` just means `succ(b)`. 

On the next level, the final level of Tutorial World, we will introduce
addition, and when we've solved it we'll be ready to enter Addition World.
-/

/- Theorem
If `a = succ(b)`, then `succ(a) = succ(succ(b))`.
-/
theorem example4 (a b : mynat) (h : a = succ b) : succ a = succ (succ b) :=
begin [less_leaky]
  rw h,
  refl,



end

end mynat -- hide
