import game.world4.level2 -- hide
namespace mynat -- hide

/- 

# Power World

## Level 3: `pow_one`
-/

/- Lemma
For all naturals $a$, $a ^ 1 = a$.
-/
lemma pow_one (a : mynat) : a ^ (1 : mynat) = a :=
begin [less_leaky]
  rw one_eq_succ_zero,
  rw pow_succ,
  rw pow_zero,
  rw one_mul,
  refl,

end

end mynat -- hide
