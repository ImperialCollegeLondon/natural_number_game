import game.world9.level1 -- hide
namespace mynat -- hide

/-
# Advanced Multiplication World

## Level 2: `eq_zero_or_eq_zero_of_mul_eq_zero`

A variant on the previous level.
-/

/- Theorem
If $ab = 0$, then at least one of $a$ or $b$ is equal to zero.
-/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :
  a = 0 ∨ b = 0 :=
begin [nat_num_game]
  cases a with d,
    left,
    refl,
  cases b with e he,
    right,
    refl,
  exfalso,
  rw mul_succ at h,
  rw add_succ at h,
  exact succ_ne_zero _ h,
end

end mynat -- hide
