import game.world4.level5 -- hide
namespace mynat -- hide

/- 

# Power World

## Level 6: `mul_pow`

You might find the tip at the end of level 9 of Multiplication World
useful in this one. You can go to the main menu and pop back into
Multiplication World and take a look -- you won't lose any of your
proofs. You'll only lose proofs if you reload the page.
-/


/- Lemma
For all naturals $a$, $b$, $n$, we have $(ab) ^ n = a ^ nb ^ n$.
-/
lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=
begin [less_leaky]
  induction n with t Ht,
    rw [pow_zero, pow_zero, pow_zero, mul_one],
    refl,
  rw [pow_succ, pow_succ, pow_succ, Ht],
  simp,

  

end

end mynat -- hide
