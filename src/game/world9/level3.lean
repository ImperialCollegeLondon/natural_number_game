import game.world9.level2 -- hide
namespace mynat -- hide

/-
# Advanced Multiplication World

## Level 3: `mul_eq_zero_iff`

Now you have `eq_zero_or_eq_zero_of_mul_eq_zero` this is pretty straightforward.
-/

/- Theorem
$ab = 0$, if and only if at least one of $a$ or $b$ is equal to zero.
-/
theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin [nat_num_game]
  split,
    swap,
    intro hab,
    cases hab,
      rw hab,
      rw zero_mul,
      refl,
    rw hab,
    rw mul_zero,
    refl,
  intro h,
  exact eq_zero_or_eq_zero_of_mul_eq_zero a b h,

  
end

end mynat -- hide
