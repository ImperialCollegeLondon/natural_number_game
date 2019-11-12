import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level4 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 5: `add_right_cancel`

The theorem `add_right_cancel` is the theorem that you can cancel on the left
when you're doing addition -- if `a + t = b + t` then `a = b`. After `intro h`
I'd recommend induction on `t`. Don't forget that `rw add_zero at h` can be used
to do rewriting of hypotheses rather than the goal.
-/


/- Theorem
On the set of natural numbers, addition has the right cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + t = b + t, $$
then we have $a = b$.
-/
theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=
begin [less_leaky]
  intro h,
  induction t with d hd,
  rw add_zero at h,
  rw add_zero at h,
  exact h,
  apply hd,
  rw add_succ at h,
  rw add_succ at h,
  exact succ_inj(h),  
end

end mynat -- hide
