import game.world4.level7 -- hide
import tactic.ring
namespace mynat -- hide

/- 

# World 4 : Power World

## Level 8 : `add_squared`

[final boss music]
-/

/- Theorem
For all naturals $a$ and $b$, we have
$$(a+b)^2=a^2+b^2+2*a*b.$$
-/
lemma add_squared (a b : mynat) :
  (a + b) ^ (succ(1)) = 
a ^ (succ(1)) + b^(succ(1)) + (succ(1))*a*b :=
begin [less_leaky]
  rw pow_succ,
  rw pow_succ,
  rw pow_succ,
  rw one_eq_succ_zero,
  rw pow_succ,
  rw pow_succ,
  rw pow_succ,
  rw pow_zero,
  rw pow_zero,
  rw pow_zero,
  rw one_mul,
  rw one_mul,
  rw one_mul,
  rw mul_add,
  rw add_mul,
  rw add_mul,
  rw succ_mul,
  rw succ_mul,
  rw zero_mul,
  rw zero_add,
  rw add_mul,
  rw mul_comm b,
  rw add_assoc,
  rw ←add_assoc (a * b),
  rw add_comm _ (b * b),
  rw ←add_assoc,
  rw ←add_assoc,
  refl,
end

/-
I just beat this level with 27 rewrites followed by a `refl`. 
Can you do any better? If you beat it then well done. Do you
fancy doing $(a+b)^3$ now? You might want to read 
<a href="https://xenaproject.wordpress.com/2018/06/13/ab3/" target="blank">
this Xena Project blog post</a> before you start though.
-/

/-
The next world is inequality world, and you are going to have to
learn two more tactics -- `cases` and `use`. Unfortunately I can
only think of a few levels before we actually have to learn about
how Lean handles implications, which is what I am currently working on.
-/

end mynat -- hide
