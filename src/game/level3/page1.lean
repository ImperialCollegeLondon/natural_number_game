import game.level1.page4
import mynat.mul


/- 
Here's what you get from the import:

1) The following data:
  * a function called mynat.mul, and notation a * b for this function

2) The following axioms:

  * `mul_zero : ∀ a : mynat, a * 0 = 0`
  * `mul_succ : ∀ a b : mynat, a * succ(b) = a * b + b`

These axiom between them tell you how to work out a * x for every x; use induction on x to
reduce to the case either `x = 0` or `x = succ b`, and then use `mul_zero` or `mul_succ` appropriately.
-/

/-
-- main goal: comm_semiring

--comm_semiring [] -- collectible_06
--  semiring [] -- collectible_05
--  {
--    add_comm_monoid -- (collectible_02)
--    monoid -- collectible_04
--      semigroup [mul_assoc]
--        (has_mul)
  --    (has_one)
  --  distrib [left_distrib, right_distrib]
--     (has_mul)
--     (has_add)
--    mul_zero_class [zero_mul, mul_zero] -- collectible_03
--     (has_mul)
--     (has_zero)
--  }
--  comm_monoid []
--    monoid (see above)
--    comm_semigroup [mul_comm]
--      semigroup (see above)
-/

namespace mynat


/- Lemma
For all natural numbers $m$, we have
$$ 0 * m = 0. $$
-/
lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin [less_leaky]
  induction m with d hd,
  {
    rw mul_zero,
    refl
  },
  {
    rw mul_succ,
    rw hd,
    rw add_zero,
    refl
  }
end

def collectible_3 : mul_zero_class mynat := by structure_helper

end mynat