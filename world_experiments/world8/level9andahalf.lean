import game.world3.level8 -- hide
import game.world2.level11 -- succ ne zero -- hide
import game.world2.level13 -- add_left_eq_zero -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 9: `mul_pos`

If you do `cases b with n` when `b` is a natural number, it will split into the
two possibilites, namely `b = 0` and `b = succ(n)`. So `cases` here is like
a weaker version of induction (you don't get the inductive hypothesis).

Understanding `intro` and `apply` will be useful here.
-/

/- Theorem
The product of two non-zero natural numbers is non-zero.
-/
theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin [less_leaky]
  intros ha hb,
  intro hab,
  cases b with b,
    apply hb,
    refl,
  rw mul_succ at hab,
  apply ha,
  cases a with a,
    refl,
  rw add_succ at hab,
  exfalso,
  apply succ_ne_zero hab
end

end mynat -- hide
