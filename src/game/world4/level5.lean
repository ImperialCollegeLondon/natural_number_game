import game.world4.level4 -- hide
namespace mynat -- hide

/- 

# World 4 : Power World

## Level 5 of 7: `pow_add`
-/

/- Lemma
For all naturals $m$, $a$, $b$, we have $m ^{a + b} = m ^ a  m ^ b$.
-/
lemma pow_add (m a b : mynat) : m ^ (a + b) = m ^ a * m ^ b :=
begin [less_leaky]
  induction b with t ht,
    rw [add_zero, pow_zero, mul_one],
    refl,
  rw [add_succ, pow_succ, pow_succ, ht, mul_assoc],
  refl,

  
end

end mynat -- hide
