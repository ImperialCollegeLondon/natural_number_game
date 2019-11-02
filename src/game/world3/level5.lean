import game.world3.level4 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 5: `mul_assoc`

Currently our tools for multiplication include the
following: 

* `mul_zero m : m * 0 = 0`
* `zero_mul m : 0 * m = 0`
* `mul_succ a b : a * succ b = a * b + a`
* `mul_add t a b : t * (a + b) = t * a + t * b`

These things above are the tools we need to prove that multiplication is associative.

## Random tactic hints

1) Did you know you can do `repeat {rw mul_succ}`?
2) Did you know you can do `rwa [hd, mul_add]`? (I learnt that trick from Ken Lee)
-/
/- Lemma
Multiplication is associative.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$$ (ab)c = a(bc). $$
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
