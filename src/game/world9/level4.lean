import game.world9.level3 -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 4: `mul_left_cancel`

This is the last of the bonus multiplication levels.
`mul_left_cancel` will be useful in inequality world.
-/

/- Theorem
If $a \neq 0$, $b$ and $c$ are natural numbers such that
$ ab = ac, $
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
      cases (eq_zero_or_eq_zero_of_mul_eq_zero _ _ hb) with h h,
        exact h,
      exfalso,
      exact succ_ne_zero _ h,
    },
    { have h : c = d,
        apply hd,
        rw mul_succ at hb,
        rw mul_succ at hb,
        apply add_right_cancel hb,
      rw h,
      refl,
    }
  }
end

end mynat -- hide

/-
To come -- inequality world. 30 levels of `≤` and the `use` tactic.
-/