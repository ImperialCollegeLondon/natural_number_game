import game.world5.level3 -- hide
namespace mynat -- hide

/-
# World 5 : Inequality world 

## Level 4 : `le_zero`

To do a level like this, you'll need to know that
if `a + c = 0` then `a = 0`. You could launch into
a proof of this e.g. via a case split on `a` (`cases a`
will split into the cases `a = 0` and `a = succ(b)`) but
actually we already proved this lemma -- it's `add_right_eq_zero`. 
If you're planning on working through world 5, you should really
check that you can do the extra levels in world 2 first. The
game designers have unlocked all these levels for you, but the
proofs will require 
-/


/- Lemma
For all naturals `a`, if `a ≤ 0` then `a = 0`.
-/
lemma le_zero {a : mynat} : a ≤ 0 → a = 0 :=
begin [less_leaky]
  intro h,
  cases h with c hc,



end

end mynat -- hide
