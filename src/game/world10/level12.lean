import game.world10.level11 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 12: `le_of_succ_le_succ`

-/

/- Lemma
For all naturals $a$ and $b$,
$\operatorname{succ}(a)\le\operatorname{succ}(b)\implies a\le b.$
-/
theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b :=
begin [less_leaky]
  intro h,
  cases h with c hc,
  use c,
  apply succ_inj,
  rw hc,
  exact succ_add a c,
end
  
end mynat -- hide
