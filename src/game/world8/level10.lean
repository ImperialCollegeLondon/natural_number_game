import mynat.definition -- hide
import mynat.add -- hide
import game.world7.level4 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 10 -- `add_right_cancel`

You have, amongst other things, these:

  * `zero_ne_succ (a : mynat) : zero ≠ succ(a)`
  * `succ_inj : (a b : mynat) : succ(a) = succ(b) → a = b`
  * `add_zero : (a : mynat) : a + 0 = a`
  * `add_succ : (a b : mynat) : a + succ(b) = succ(a + b)`
  * `zero_add : (a : mynat) : 0 + a = a`
  * `add_assoc : (a b c : mynat) (a + b) + c = a + (b + c)`
  * `succ_add : (a b : mynat) : succ a + b = succ (a + b)`
  * `add_comm : (a b : mynat) : a + b = b + a`
  * `add_left_cancel (a b c : mynat) : a + b = a + c → b = c`

Tactic info at <a href="http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html" target="blank">tactic guide</a>.

`add_right_cancel` can be deduced from `add_left_cancel`. You might find the fact that `rw add_comm at h` will change `x + y` into `y + x` *in the hypothesis h*. 
-/


/- Theorem
On the set of natural numbers, addition has the right cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + t = b + t, $$
then we have $a = b$.
-/
theorem add_right_cancel {a b t : mynat} : a + t = b + t → a = b :=
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
