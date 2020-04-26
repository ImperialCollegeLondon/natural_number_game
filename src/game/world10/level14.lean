import game.world10.level13 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 14: `add_le_add_left`

I know these are easy and we've done several already, but this is one
of the axioms for an ordered commutative monoid! The nature of formalising
is that we should formalise all "obvious" lemmas, and then when we're
actually using $\le$ in real life, everything will be there. Note also,
of course, that all of these lemmas are already formalised in Lean's
maths library already, for Lean's inbuilt natural numbers. 
-/

/- Lemma
If $a\le b$ then for all $t$, $t+a\le t+b$. 
-/
theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=
begin [nat_num_game]
  cases h with c hc,
  use c,
  rw hc,
  ring,


end


end mynat -- hide
