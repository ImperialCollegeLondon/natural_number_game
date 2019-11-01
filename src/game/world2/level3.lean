import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level2 -- hide
namespace mynat -- hide

/- 
# World 2 -- addition world

## Level 3 : `succ_add`

## You are equipped with:

  * `add_zero (a : mynat) : a + 0 = a`
  * `add_succ (a b : mynat) : a + succ(b) = succ(a + b)`
  * `zero_add (a : mynat) : 0 + a = a`
  * `add_assoc (a b c : mynat) : (a + b) + c = a + (b + c)`

Oh no! On the way to `add_comm`, a wild `succ_add` appears. `succ_add`
is the statement that `succ(a) + b = succ(a + b)` for `a` and `b` in your
natural number type. You will
need this theorem to prove `a + b = b + a` so you'd better prove it first.
NB: think about why computer scientists called this result `succ_add` .
There is a logic to all the names.

Note that if you want to be more precise about exactly where you want
to rewrite something like `add_succ`, you can do things like `rw add_succ (succ a)` or
`rw add_succ (succ a) d`, telling Lean explicitly what to use for
the input variables for the function `add_succ`. Indeed, `add_succ`
is a function -- it takes as input two variables `a` and `b` and outputs a proof
that `a + succ(b) = succ(a + b)`. The tactic `rw add_succ` just says to Lean "guess
what the variables are". 
-/

/- Lemma
For all natural numbers $a, b$, we have
$$ \operatorname{succ}(a) + b = \operatorname{succ}(a + b). $$
-/
lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin [less_leaky]
  induction b with d hd,
  {
    refl
  }, 
  { rw add_succ,
    rw hd,
    rw add_succ,
    refl
  }
end

end mynat -- hide 
