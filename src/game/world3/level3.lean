import game.world3.level2 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 3: `one_mul`

Currently our tools for multiplication are the
following: 

* `mul_zero : ∀ m, m * 0 = 0`
* `zero_mul : ∀ m, 0 * m = 0`
* `mul_succ : ∀ a b, a * succ b = a * b + b`
* `mul_one ; ∀ m, m * 1 = 1`

We have also these other facts about 1 (the
first is just the definition, the second was
world 2 level 5)

* `one_eq_succ_zero : 1 = succ(0)`
* `succ_eq_add_one : ∀ a, succ(a) = a + 1` 

We just proved mul_one, now let's prove one_mul. 
Then we will have proved, in fancy terms,
that 1 is a "left and right identity"
for multiplication (just like we showed that
0 is a left and right identity for addition
with `add_zero` and `zero_add`).
-/

/- Lemma
For any natural number $m$, we have
$$ 1 * m = m. $$
-/
lemma one_mul (m : mynat) : 1 * m = m :=
begin [less_leaky]
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
