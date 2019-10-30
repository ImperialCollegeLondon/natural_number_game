import game.world4.level6 -- hide
namespace mynat -- hide

/- 

# World 4 : Power World

## Level 7 of 7: `pow_pow`
-/

/-
Boss level! What will the collectible be?
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

/-
Apparently Lean can't find a collectible, even though you feel like you
just finished power world so you must have proved *something*. What should the
collectible for this level be called? 
-/

/-
The next world is inequality world, but it's different. Before you
go there, you really should do world 2 level 6 and a half, and
learn the terrifying truth about how our proofs go forwards but
their functions go backwards. You will learn about `have`, the way
to swim upstream, and `have` is the only tool you really need.
Computer scientists have made tools that do proofs backwards,
and this is quite a weird way of thnking about proofs. 
-/

end mynat -- hide
