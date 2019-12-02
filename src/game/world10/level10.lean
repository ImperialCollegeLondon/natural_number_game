import game.world10.level9 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 10: `le_succ_self`

Can you find the two-line proof?
-/

/- Lemma
For all naturals $a$, $a\le\operatorname{succ}(a).$
-/
lemma le_succ_self (a : mynat) : a ≤ succ a :=
begin [nat_num_game]
  use 1,
  refl,
  

end

end mynat -- hide
