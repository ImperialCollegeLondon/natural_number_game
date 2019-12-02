import game.world4.level4 -- hide
namespace mynat -- hide

/- 

# Power World

## Level 5: `pow_add`
-/

/- Lemma
For all naturals $m$, $a$, $b$, we have $a^{m + n} = a ^ m  a ^ n$.
-/
lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n :=
begin [nat_num_game]
  induction n with t ht,
    rw [add_zero, pow_zero, mul_one],
    refl,
  rw [add_succ, pow_succ, pow_succ, ht, mul_assoc],
  refl,

  

  
end

end mynat -- hide
