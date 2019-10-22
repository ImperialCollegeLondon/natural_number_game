import game.world3.level9 -- hide
import game.world2.level7 -- succ ne zero -- hide
import game.world2.level13 -- add_left_eq_zero -- hide

namespace mynat -- hide

/-
A variant on the previous level.
-/

/- Theorem
If $a * b = 0$, then at least one of $a$ or $b$ is equal to zero.
-/
theorem eq_zero_or_eq_zero_of_mul_eq_zero ⦃a b : mynat⦄ (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin [less_leaky]
  cases a with d,
    left, refl,
  cases b with e he,
    right, refl,
  exfalso,
  rw mul_succ at h,
  rw add_succ at h,
  exact succ_ne_zero h,
end

end mynat -- hide
