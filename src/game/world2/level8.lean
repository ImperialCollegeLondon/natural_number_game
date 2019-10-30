import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level7 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 8 -- `eq_iff_succ_eq_succ`

Here is an `iff` goal. You can split it into two goals (the implications in both
directions) using the `split` tactic, which you should probably start with.
You are also going to have to learn something about tactics which handle
the basics of propositions and their proofs here. You will need to know the
`intro` tactic, which works (only) on a goal
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
