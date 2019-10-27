import game.world3.level12 -- hide
import game.world2.level13 -- add_left_eq_zero -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 13: `mul_right_comm`

This is the last of the bonus multiplication levels.
`mul_right_comm` will be useful in power world. 
The proof is basically the same as `add_right_comm`. 
See how few lines you can do it in.
-/

/- Theorem
For all $a$, $b$, $c$ natural numbers, $(a \times b) \times c = (a \times c) \times b$.
-/
theorem mul_right_comm (a b c : mynat) : a * b * c = a * c * b :=
begin [less_leaky]
  rw mul_assoc,
  rw mul_comm b,
  rw mul_assoc,
  refl,
end

/- To come: Powers! Inequalities! Odd and even numbers! Congruences!
Prime numbers! And any other mathematics with the natural numbers that anyone can think of. 
Suggestions welcome to k.buzzard@imperial.ac.uk or find me on the Lean chat at Zulip.
-/

end mynat -- hide
