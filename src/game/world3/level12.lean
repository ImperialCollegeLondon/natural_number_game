import game.world3.level11 -- hide
import game.world2.level13 -- add_left_eq_zero -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 12: `mul_left_cancel`

This is the last but one of the bonus multiplication levels.
`mul_left_cancel` will be useful in inequality world.
But before that we have a relatively short power world.
-/

/- Theorem
If $a \neq 0$, $b$ and $c$ are natural numbers such that
$$ a \times b = a \times c, $$
then $b = c$.
-/
theorem mul_left_cancel ⦃a b c : mynat⦄ (ha : a ≠ 0) : a * b = a * c → b = c :=
begin [less_leaky]
  revert b,
  induction c with d hd,
  { intro b,
    rw mul_zero,
    intro h,
    cases (eq_zero_or_eq_zero_of_mul_eq_zero h),
      exfalso,
      apply ha,
      assumption,
    assumption
  },
  { intros b hb,
    cases b with c,
    { rw mul_zero at hb,
      rw mul_succ at hb,
      exfalso,
      apply ha,
      rw eq_comm at hb,
      apply add_left_eq_zero hb,
    },
    { congr, -- c = d -> succ c = succ d
      apply hd,
      rw mul_succ at hb,
      rw mul_succ at hb,
      apply add_right_cancel hb
    }
  }
end

end mynat -- hide
