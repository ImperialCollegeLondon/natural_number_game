import game.world10.level13 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 15: `add_le_add_left`

I know these are easy and we've done several already, but this is one
of the axioms for an ordered commutative monoid! 
-/

/- Lemma
If $a\le b$ then for all $t$, $t+a\le t+b$. 
-/
theorem add_le_add_left (a b : mynat) (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=
begin [less_leaky]
  cases h with c hc,
  use c,
  rw hc,
  ring,


end


end mynat -- hide
