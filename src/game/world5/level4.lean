import game.world5.level3 -- hide
import game.world2.level14 -- add_right_eq_zero
namespace mynat -- hide

/-
# World 5 : Inequality world 

## Level 4 : `le_zero`

To do a level like this, you'll need to know that
if `a + c = 0` then `a = 0`. You could launch into
a proof of this e.g. via a case split on `a` (`cases a`
will split into the cases `a = 0` and `a = succ(b)`) but
actually we already proved this lemma -- it's `add_right_eq_zero`
from the extra levels in world 2 (it's level 14). 
If you're planning on working through world 5, you should probably
check that you can do the extra levels in world 2 first.

oh -- start with `intro h`. You should have picked up stuff about
the `intro` tactic in the world 2 extra levels. 
-/

/-

Pro tip: if `h` is a proof of `A = B`, then `h.symm` is a proof of `B = A`.
-/

/- Lemma
For all naturals `a`, if `a ≤ 0` then `a = 0`.
-/
lemma le_zero {a : mynat} (h : a ≤ 0) : a = 0 :=
begin [less_leaky]
  cases h with c hc,
  apply add_right_eq_zero hc.symm,


end

end mynat -- hide
