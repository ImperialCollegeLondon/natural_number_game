import mynat.definition -- hide
namespace mynat -- hide

/-

## Tutorial level 4: more rewriting.

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
See if you can do it -- more explanations are below the example.
-/

/- Theorem
If `a = succ(b)`, then `succ(a) = succ(succ(b))`.
-/
theorem example4 (a b : mynat) (h : a = succ b) : succ a = succ (succ b) :=
begin [less_leaky]
  rw h,
  refl,



end

/- Click
on the button, delete the sorry, replace with `rw h,` (*don't forget the comma*) and
see how the `a` in the goal changes to `succ b`. Both sides of the equality are
now exactly the same, so you should now be able to close the goal with `refl,`. 

Notice that the system sometimes drops brackets when they're not necessary.
`succ a` just means `succ(a)`.

On the next page, the final page of this introductory world, we will introduce
addition. 
-/

end mynat
