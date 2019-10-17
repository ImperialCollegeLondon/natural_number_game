import game.level2.page5 -- hide
import mynat.mul

/- 
This new import gives you the definition of multiplication on your
natural numbers. It is defined by recursion, just like addition.
Here are the two new axioms:

  * `mul_zero : ∀ a : mynat, a * 0 = 0`
  * `mul_succ : ∀ a b : mynat, a * succ(b) = a * b + b`

You can keep all the theorems you proved about addition, but 
for multiplication, that's all you've got right now.
Like addition, we need to go for the proofs that multiplication
is commutative and associative, but as well as that we will
need to prove facts about the relationship between multiplication
and addition, for example `a * (b + c) = a * b + a * c`, so now
there is a lot more to do. Good luck! 
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