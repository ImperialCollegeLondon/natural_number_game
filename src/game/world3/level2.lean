import game.world3.level1 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 2: `mul_one`

Currently our tools for multiplication are the
following: 

* `mul_zero (m : mynat) : m * 0 = 0`
* `zero_mul (m : mynat) : 0 * m = 0`
* `mul_succ (a b : mynat) : a * succ b = a * b + a`

We also have

* `one_eq_succ_zero : 1 = succ(0)`

which was mentioned way back in Tutorial World and
which will be a useful thing to rewrite right now, as we
begin to prove a couple of lemmas about how `1` behaves
with respect to multiplication.
-/

/- Lemma
For any natural number $m$, we have
$$ m \times 1 = m. $$
-/
lemma mul_one (m : mynat) : m * 1 = m :=
begin [less_leaky]
  rw one_eq_succ_zero,
  rw mul_succ,
  rw mul_zero,
  rw zero_add,
  refl

  
end

end mynat -- hide
