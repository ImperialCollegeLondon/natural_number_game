import game.world3.level13 -- hide
import mynat.pow -- new import
namespace mynat -- hide

/- 

# World 4 : Power World

A new import! This import gives you the power to make powers on your
natural numbers. It is defined by recursion, just like addition and multiplication.
Here are the two new axioms:

  * `pow_zero : ∀ a : mynat, a ^ 0 = 0`
  * `pow_succ : ∀ a b : mynat, a ^ succ(b) = a ^ b * b`

The power function has various relations to addition and multiplication.
The usual tactics `induction`, `rw` and `refl` should get you through this world
completely without too much trouble.

The levels in this world were designed by Sian Carey, a UROP student
at Imperial in the summer of 2019.

## Level 1 : `zero_pow_zero`
-/

/- Lemma
$0 ^ 0 = 1$.
-/
lemma zero_pow_zero : (0 : mynat) ^ (0 : mynat) = 1 :=
begin [less_leaky]
  rw pow_zero,
  refl,


end

end mynat -- hide
