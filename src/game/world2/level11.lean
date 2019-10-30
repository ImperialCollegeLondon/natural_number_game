import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level10 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 11 -- `add_right_cancel_iff`

You have (amongst other things) these:

  * `zero_ne_succ (a : mynat) : zero ≠ succ(a)`
  * `succ_inj (a b : mynat) : succ(a) = succ(b) → a = b`
  * `add_zero (a : mynat) : a + 0 = a`
  * `add_succ (a b : mynat) : a + succ(b) = succ(a + b)`
  * `zero_add (a : mynat) : 0 + a = a`
  * `add_assoc (a b c : mynat) : (a + b) + c = a + (b + c)`
  * `succ_add (a b : mynat) : succ a + b = succ (a + b)`
  * `add_comm (a b : mynat) : a + b  = b + a`
  * `add_right_cancel (a b c : mynat) : a + b = c + b → a = c`

It's sometimes convenient to have the "if and only if" version
of theorems like `add_right_cancel`. Remember that you can use `split`
to split an ↔ goal into the → goal and the ← goal.
-/

/- Theorem
Addition has the left cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + t = b + t, $$
then we have $a = b$.
-/
theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=
begin [less_leaky]
  split,
  { apply add_right_cancel}, -- done that way already,
  { intro H, -- H : a = b,
    rw H,
    refl,
  }
end

end mynat -- hide
