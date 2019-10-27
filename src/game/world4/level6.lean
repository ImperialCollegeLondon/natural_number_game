import game.world4.level5 -- hide
namespace mynat -- hide

/- 

# World 4 : Power World

## Level 6 of 7: `mul_pow`

You might find `mul_right_comm` useful in this one. Remember `rw mul_right_comm (m ^ t)` will
rewrite the first occurrence of `(m ^ t) * x * y = (m ^ t) * y * x`.
-/


/- Lemma
For all naturals $m$, $n$, $a$, we have $(m \times n) ^ a = m ^ a \times n ^ a$.
-/
lemma mul_pow (m n a : mynat) : (m * n) ^ a = m ^ a * n ^ a :=
begin [less_leaky]
  induction a with t Ht,
    rw [pow_zero, pow_zero, pow_zero, mul_one],
    refl,
  rw [pow_succ, pow_succ, pow_succ, Ht],
  rw ←mul_assoc,
  rw mul_right_comm (m ^ t),
  rw ←mul_assoc,
  refl,

end

end mynat -- hide
