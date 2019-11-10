import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level11 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 14 -- `add_right_eq_zero`

You have
  * `add_left_eq_zero (a b : mynat) a + b = 0 → b = 0`

  from level 13, so `add_right_eq_zero` shouldn't be too hard.
-/

/- Lemma
If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $a = 0$.
-/
lemma add_right_eq_zero {{a b : mynat}} : a + b = 0 → a = 0 :=
begin [less_leaky]
  intro H,
  rw add_comm at H,
  exact add_left_eq_zero H,
end

end mynat -- hide
