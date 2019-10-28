import game.world2.level6 -- hide
import mynat.mul

/- 

# World 3

A new import! This import gives you the definition of multiplication on your
natural numbers. It is defined by recursion, just like addition.
Here are the two new axioms:

  * `mul_zero : ∀ a : mynat, a * 0 = 0`
  * `mul_succ : ∀ a b : mynat, a * succ(b) = a * b + b`

In words, we define multiplication by "induction on the second variable",
with `a * 0` defined to be `0` and, if we know `a * b`, then `a` times
the number after `b` is defined to be `a * b + b`. 

You can keep all the theorems you proved about addition, but 
for multiplication, those two results above are all you've got right now.
Like addition, we need to go for the proofs that multiplication
is commutative and associative, but as well as that we will
need to prove facts about the relationship between multiplication
and addition, for example `a * (b + c) = a * b + a * c`, so now
there is a lot more to do. Good luck! 

We are given `mul_zero`, and the first thing to prove is `zero_mul`.
Like `zero_add`, we of course prove it by induction.

## World 3 Level 1 : `zero_mul`
-/

namespace mynat -- hide

/- Lemma
For all natural numbers $m$, we have
$$ 0 * m = 0. $$
-/
lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin [less_leaky]
  induction m with d hd,
  {
    rw mul_zero,
    refl
  },
  {
    rw mul_succ,
    rw hd,
    rw add_zero,
    refl
  }
end

end mynat -- hide
