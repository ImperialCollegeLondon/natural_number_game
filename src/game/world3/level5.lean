import game.world3.level4 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 5: `mul_assoc`

Currently our tools for multiplication include the
following: 

* `mul_zero m : m * 0 = 0`
* `zero_mul m : 0 * m = m`
* `mul_succ a b : a * succ b = a * b + b`
* `mul_add t a b : t * (a + b) = t * a + t * b`

These things above are the tools we need to prove that multiplication is associative.
-/

/- Lemma
Multiplication is associative.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$$ (a * b) * c = a * (b * c). $$
-/
lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin [less_leaky]
  induction c with d hd,
  { 
    repeat {rw mul_zero},
  },
  {
    rw mul_succ,
    rw mul_succ,
--    show (a * b) * d + (a * b) = _,
    rw hd,
--    show _ = a * (b * d + _),
    rw mul_add,
    refl,
  }
end

/-
A mathematician could now remark that you have proved that the natural
numbers form a monoid under multiplication.
-/
def collectible_4 : monoid mynat := by structure_helper -- hide

end mynat -- hide
