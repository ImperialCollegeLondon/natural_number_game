import mynat.definition -- hide
import mynat.add -- hide
import game.world7.level14 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 15 -- `eq_zero_of_add_right_eq_self`

We have

  * `succ_eq_add_one (n : mynat) : succ n = n + 1`

but sometimes the other way is also convenient.
-/

/- Theorem
For any natural number $d$, we have
$$ d+1 = \operatorname{succ}(d). $$
-/
theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin [less_leaky]
  rw succ_eq_add_one,
  refl,



end

end mynat -- hide
