import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level6andseveneighths -- hide
namespace mynat -- hide

/- Tactic : split
The `split` tactic turns one "if and only if" goal into
two goals corresponding to the implications in each
direction.

### Example:

If your local context (the top right window) looks like this
```
a b : mynat,
⊢ a = b ↔ a + 3 = b + 3
```

then after

`split,`

it will look like this:

```
2 goals
a b : mynat
⊢ a = b → a + 3 = b + 3

a b : mynat
⊢ a + 3 = b + 3 → a = b
```
-/

/-

# World 2 -- Addition World

## Level 8 -- `eq_iff_succ_eq_succ`

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
theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
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
