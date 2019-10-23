import game.world5.level5 -- hide
namespace mynat -- hide

/-
# World 5 : Inequality world 

## Level 6 : `le_antisymm`

In this level, it would be helpful if you knew about how to create extra
hypotheses in the middle of a proof.

Say you have a hypothesis `h : a + b = a`

and you remember back from world 2 level 12 that you proved

`eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0`.

You can think of `eq_zero_of_add_right_eq_self` as a function
which turns proofs of `a + b = a` into proofs of `b = 0`. So you can
use the `have` tactic, and type

`have h2 := eq_zero_of_add_right_eq_self h,`

and now `h2` will be a proof that `b = 0`. 

Also don't forget that you can use the `rw` tactic on hypotheses -- `rw h1 at h2`
will replace occurrences of the left hand side of `h1` in `h2`,
with the right hand side.
-/



/- Lemma
≤ is antisymmetric. In other words, if a ≤ b and b ≤ a then a = b. 
-/
theorem le_antisymm {{a b : mynat}} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
begin [less_leaky]
  cases hab with c hc,
  cases hba with d hd,
  rw hd at hc,
  rw add_assoc at hc,
  have h := eq_zero_of_add_right_eq_self hc.symm,
  have h2 := add_right_eq_zero h,
  rw h2 at hd,
  rw add_zero at hd,
  assumption,


end

/-
Congratulations -- you just proved that the natural numbers are a partial order!

To come: about 25 more ≤ levels. But that will have to wait for v1.1.
If you got this far, and did the world 2 and 3 extra levels, then you have
beaten the game. Now think of a simple mathematical theorem, and see if you
can formulate and prove it yourself using the Lean Theorem Prover. Download Lean
and its maths library
<a href="https://github.com/leanprover-community/mathlib" target=blank">here</a>
(please follow the installation instructions to the letter)
and if and when you get stuck, come and ask at
<a href="https://leanprover.zulipchat.com" target=blank">the Lean chat</a>.
-/

instance : partial_order mynat := by structure_helper -- hide
end mynat

