import game.world5.level2 -- hide
namespace mynat -- hide

/-
# World 5 : Inequality world 

## Level 3 : `zero_le`

-/

/- Lemma
For all naturals $a$, $0\leq a$.
-/
lemma zero_le (a : mynat) : 0 ≤ a :=
begin [less_leaky]
  use a,
  rw zero_add,
  refl,


end

end mynat -- hide
