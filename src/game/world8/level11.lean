import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level10 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 11: `add_right_eq_zero`

We just proved `add_left_eq_zero (a b : mynat) : a + b = 0 → b = 0`.
Hopefully `add_right_eq_zero` shouldn't be too hard now.
-/

/- Lemma
If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $a = 0$.
-/
lemma add_right_eq_zero (a b : mynat) : a + b = 0 → a = 0 :=
begin [nat_num_game]
  intro H,
  rw add_comm at H,
  exact add_left_eq_zero _ _ H,
end

end mynat -- hide
