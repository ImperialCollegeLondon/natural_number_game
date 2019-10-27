import game.world3.level1 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 2: `mul_one`

Currently our tools for multiplication are the
following: 

* `mul_zero : ∀ m, m * 0 = 0`
* `zero_mul : ∀ m, 0 * m = m`
* `mul_succ : ∀ a b, a * succ b = a * b + b`

We also have

* `one_eq_succ_zero : 1 = succ(0)`

which will be a useful thing to rewrite as we now
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
  exact zero_add m,
end

end mynat -- hide
