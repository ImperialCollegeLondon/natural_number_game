import game.world9.level3 -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 4: `mul_left_cancel`

This is the last but one of the bonus multiplication levels.
`mul_left_cancel` will be useful in inequality world.
-/

example (h : 3 = 4) : 2 + 2 = 4 :=
begin
  symmetry,
  symmetry' at h,
end

/- Theorem
If $a \neq 0$, $b$ and $c$ are natural numbers such that
$$ a * b = a * c, $$
then $b = c$.
-/
theorem mul_left_cancel (a b c : mynat) (ha : a ≠ 0) : a * b = a * c → b = c :=
begin [less_leaky]
  revert b,
  induction c with d hd,
  { intro b,
    rw mul_zero,
    intro h,
    cases (eq_zero_or_eq_zero_of_mul_eq_zero _ _ h) with h1 h2,
      exfalso,
      apply ha,
      assumption,
    assumption
  },
  { intros b hb,
    cases b with c,
    { rw mul_zero at hb,
      exfalso,
      apply ha,
      symmetry at hb,
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
