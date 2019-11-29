import game.world8.level5 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 6: `add_left_cancel`

The theorem `add_left_cancel` is the theorem that you can cancel on the left
when you're doing addition -- if `t + a = t + b` then `a = b`. 
There is a three-line proof which ends in `exact add_right_cancel a t b` (or even
`exact add_right_cancel _ _ _`); this
strategy involves changing the goal to the statement of `add_right_cancel` somehow.


-/


/- Theorem
On the set of natural numbers, addition has the left cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + b = a + c, $$
then we have $b = c$.
-/
theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b :=
begin [less_leaky]
  rw add_comm,
  rw add_comm t,
  exact add_right_cancel a t b,



end

end mynat -- hide
