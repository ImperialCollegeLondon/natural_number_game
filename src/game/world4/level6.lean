import game.world4.level5 -- hide
namespace mynat -- hide

/- 

# World 4 : Power World

## Level 6 of 7: `mul_pow`

You might find `mul_right_comm` useful in this one. This is proved
in 3-13, but it should be in the basic world. When the big reordering
comes in v1.1 this will be in the right place.
Remember `rw mul_right_comm (a ^ t)` will
rewrite the first occurrence of `(a ^ t) * x * y = (a ^ t) * y * x`.
-/


/- Lemma
For all naturals $a$, $b$, $n$, we have $(a * b) ^ n = a ^ n * b ^ n$.
-/
lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=
begin [less_leaky]
  induction n with t Ht,
    rw [pow_zero, pow_zero, pow_zero, mul_one],
    refl,
  rw [pow_succ, pow_succ, pow_succ, Ht],
  rw ←mul_assoc,
  rw mul_right_comm (a ^ t),
  rw ←mul_assoc,
  refl,

  

end

end mynat -- hide
