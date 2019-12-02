import game.world3.level5 -- hide
import mynat.mul -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 6: `succ_mul`

We now begin our journey to `mul_comm`, the proof that `a * b = b * a`. 
We'll get there in level 8. Until we're there, it is frustrating
but true that we cannot assume commutativity. We have `mul_succ`
but we're going to need `succ_mul` (guess what it says -- maybe you
are getting the hang of Lean's naming conventions). 

Remember also that we have tools like

* `add_right_comm a b c : a + b + c = a + c + b` 

These things are the tools we need to slowly build up the results
which we will need to do mathematics "normally". 
We also now have access to Lean's `simp` tactic,
which will solve any goal which just needs a bunch
of rewrites of `add_assoc` and `add_comm`. Use if
you're getting lazy!
-/

/- Lemma
For all natural numbers $a$ and $b$, we have
$$ \operatorname{succ}(a) \times b = ab + b. $$
-/
lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin [nat_num_game]
  induction b with d hd,
  {
    rw mul_zero,
    rw mul_zero,
    rw add_zero,
    refl,
  },
  {
    rw mul_succ,
    rw mul_succ,
    rw hd,
    rw add_succ,
    rw add_succ,
    rw add_right_comm,
    refl,
  }
end

end mynat -- hide
