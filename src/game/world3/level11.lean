import game.world3.level10 -- hide
import game.world2.level7 -- succ ne zero -- hide
import game.world2.level13 -- add_left_eq_zero -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 11: `mul_eq_zero_iff`

Now you have `eq_zero_or_eq_zero_of_mul_eq_zero` this is pretty straightforward.
-/

/- Theorem
$a * b = 0$, if and only if at least one of $a$ or $b$ is equal to zero.
-/
theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin [less_leaky]
  split, swap,
    intro hab, cases hab,
      rw hab, rw zero_mul, refl,
    rw hab, rw mul_zero, refl,
  intro h,
  exact eq_zero_or_eq_zero_of_mul_eq_zero h,
end

end mynat -- hide
