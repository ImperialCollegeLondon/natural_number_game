import game.world8.level6 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 7: `add_right_cancel_iff`

It's sometimes convenient to have the "if and only if" version
of theorems like `add_right_cancel`. Remember that you can use `split`
to split an `↔` goal into the `→` goal and the `←` goal.
-/

/- Theorem
For all naturals $a$, $b$ and $t$, 
$$ a + t = b + t\iff a=b. $$
-/
theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=
begin [less_leaky]
  split,
  { exact add_right_cancel}, -- done that way already,
  { intro H, -- H : a = b,
    rw H,
    refl,
  }



end

end mynat -- hide
