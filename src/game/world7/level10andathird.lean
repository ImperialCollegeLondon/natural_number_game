import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level10 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 7 -- `succ_ne_zero`

Levels 7 to 16 are some more advanced facts about addition. If you want
to see what theorems or tactics you have, look in the drop-down menus on the left.

If you just want to skip these and move straight on to multiplication,
click on "next world" on the top right. The four tactics `refl`, `exact`,
`rw` and `induction` will get you through to the boss, `a * b = b * a`.
If you want to stick with addition world and prove some trickier goals,
you can, but you'll need to know some more tactics. For
example the `symmetry` tactic can be used whenever the goal is
a proposition defined by a symmetric binary relation, such as `=` or `≠`. 
Remember we already have `zero_ne_succ`, which here should be thought
of as a *function* which takes
as input a natural number `m` and outputs a proof that `zero ≠ succ(m)`.

If you want to venture further into
these bonus levels, you will almost certainly need the
<a href="http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html" target="blank">tactic guide</a>,
but I'll give you some hints along the way. If you are still totally stuck, ask
at <a href="https://leanprover.zulipchat.com" target="blank">the Lean chat</a> in the new users stream.
-/

/- Theorem
Zero is not the successor of any natural number.
-/
theorem succ_ne_zero {{a : mynat}} : succ a ≠ 0 := 
begin [less_leaky]
  symmetry,
  exact zero_ne_succ a,


end

end mynat
