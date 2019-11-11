import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level3 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 4: `eq_iff_succ_eq_succ`

Here is an `iff` goal. You can split it into two goals (the implications in both
directions) using the `split` tactic, which is how you're going to have to start.

`split,`

Now you have two goals. The first is exactly `succ_inj` so you can close
it with

`exact succ_inj,`

and the second one you could solve by looking up the name of the theorem
you proved in the last level and doing `exact <that name>`, or alternatively
you could get some more `intro` practice and seeing if you can prove it
using `intro`, `rw` and `refl`.
-/

/- Theorem
Two natural numbers are equal if and only if their successors are equal.
-/
theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b :=
begin [less_leaky]
  split,
  { exact succ_inj},
--  exact succ_eq_succ_of_eq,
  { intro H,
    rw H,
    refl,
  }


end

end mynat -- hide
