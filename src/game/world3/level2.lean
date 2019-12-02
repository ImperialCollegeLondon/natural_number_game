import game.world3.level1 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 2: `mul_one`

Remember that you can see everything you have proved so far about multiplication in
the drop-down box on the left (and that this list will grow as we proceed).

In this level we'll need to use

* `one_eq_succ_zero : 1 = succ(0)`

which was mentioned back in Addition World and
which will be a useful thing to rewrite right now, as we
begin to prove a couple of lemmas about how `1` behaves
with respect to multiplication.
-/

/- Lemma
For any natural number $m$, we have
$$ m \times 1 = m. $$
-/
lemma mul_one (m : mynat) : m * 1 = m :=
begin [nat_num_game]
  rw one_eq_succ_zero,
  rw mul_succ,
  rw mul_zero,
  rw zero_add,
  refl

  
end

end mynat -- hide
