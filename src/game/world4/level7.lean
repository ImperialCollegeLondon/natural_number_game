import game.world4.level6 -- hide
namespace mynat -- hide

/- 

# World 4 : Power World

## Level 7: `pow_pow`
-/

/- Lemma
For all naturals $m$, $a$, $b$, we have $(m ^ a) ^ b = m ^ {ab}$.
-/
lemma pow_pow (m a b : mynat) : (m ^ a) ^ b = m ^ (a * b) :=
begin [less_leaky]
  induction' b with t Ht,
    rw [mul_zero, pow_zero, pow_zero],
    refl,
  rw [pow_succ, Ht, mul_succ, pow_add],
  refl,




end

end mynat -- hide
