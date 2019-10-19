import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level7 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 8 -- `eq_iff_succ_eq_succ`

You have these:

  * zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)
  * succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b
  * add_zero : ∀ a : mynat, a + 0 = a
  * add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)
  * zero_add : ∀ a : mynat, 0 + a = a`
  * add_assoc : ∀ a b c : mynat, (a + b) + c = a + (b + c)
  * succ_add : ∀ a b : mynat, succ a + b = succ (a + b)
  * add_comm : ∀ a b : mynat, a + b = b + a

Here is an `iff` goal. You can split it into two goals (the implications in both
directions) using the `split` tactic, which you should probably start with.
You will also need to know the `intro` tactic, which works (only) on a goal
of the form `P → Q`; given a goal of this form, `intro h` makes `h` a proof
of `P` and changes the goal to `Q`.

-/

/- Theorem
Two natural numbers are equal if and only if their successors are equal.
-/
theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
begin [less_leaky]
  split,
  { exact succ_inj},
  { intro H,
    rw H,
    refl,
  }
end

end mynat -- hide
