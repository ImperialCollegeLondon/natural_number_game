import game.world4.level3 -- hide
namespace mynat -- hide

/- 

# Power World

## Level 4: `one_pow`
-/

/- Lemma
For all naturals $m$, $1 ^ m = 1$.
-/
lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin [nat_num_game]
  induction m with t ht,
    rw pow_zero,
    refl,
  rw pow_succ,
  rw ht,
  rw mul_one,
  refl,

end

end mynat -- hide
