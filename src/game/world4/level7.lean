import game.world4.level6 -- hide
namespace mynat -- hide

/- 

# World 4 : Power World

## Level 7 : `pow_pow`
-/

/-
Boss level! What will the collectible be?
-/
/- Lemma
For all naturals $a$, $m$, $n$, we have $(a ^ m) ^ n = a ^ {mn}$.
-/
lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) :=
begin [less_leaky]
  induction' n with t Ht,
    rw [mul_zero, pow_zero, pow_zero],
    refl,
  rw [pow_succ, Ht, mul_succ, pow_add],
  refl,






end

/-
Apparently Lean can't find a collectible, even though you feel like you
just finished power world so you must have proved *something*. What should the
collectible for this level be called? 
-/

/-
But what is this? It's one of those twists where there's another
boss after the boss you thought was the final boss! Go to the next
level!
-/

end mynat -- hide
