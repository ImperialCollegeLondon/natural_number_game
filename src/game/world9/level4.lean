import game.world9.level3 -- hide
namespace mynat -- hide

/-
# Advanced Multiplication World

## Level 4: `mul_left_cancel`

This is the last of the bonus multiplication levels.
`mul_left_cancel` will be useful in inequality world.

It might be worth noting that `revert` is the opposite of `intro`.
`revert b` can be a convenient tactic just before the beginning of
an induction proof.
-/

/- Theorem
If $a \neq 0$, $b$ and $c$ are natural numbers such that
$ ab = ac, $
then $b = c$.
-/
theorem mul_left_cancel (a b c : mynat) (ha : a ≠ 0) : a * b = a * c → b = c :=
begin [nat_num_game]
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
        apply add_right_cancel _ _ _ hb,
      rw h,
      refl,
    }
  }
end

end mynat -- hide

/-
You should now be ready for inequality world.
-/

/- Tactic : revert

## Summary

`revert x` is the opposite to `intro x`.

## Details

If the tactic state looks like this

```
P Q : Prop,
h : P
⊢ Q
```

then `revert h` will change it to

```
P Q : Prop
⊢ P → Q
```

`revert` also works with things like natural numbers: if
the tactic state looks like this

```
m : mynat
⊢ m + 1 = succ m
```

then `revert m` will turn it into

```
⊢ ∀ (m : mynat), m + 1 = mynat.succ m
```

-/
