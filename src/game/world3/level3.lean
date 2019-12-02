import game.world3.level2 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 3: `one_mul`

These proofs from addition world might be useful here:

* `one_eq_succ_zero : 1 = succ(0)`
* `succ_eq_add_one a : succ(a) = a + 1` 

We just proved `mul_one`, now let's prove `one_mul`. 
Then we will have proved, in fancy terms,
that 1 is a "left and right identity"
for multiplication (just like we showed that
0 is a left and right identity for addition
with `add_zero` and `zero_add`).
-/

/- Lemma
For any natural number $m$, we have
$$ 1 \times m = m. $$
-/
lemma one_mul (m : mynat) : 1 * m = m :=
begin [nat_num_game]
  induction m with d hd,
  {
    rw mul_zero,
    refl,
  },
  {
    rw mul_succ,
    rw hd,
    rw succ_eq_add_one,
    refl,
  }
end

end mynat -- hide
