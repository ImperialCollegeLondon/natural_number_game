import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level2 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 3: `succ_eq_succ_of_eq`.
-/

/-
We are going to prove something completely obvious: if $a=b$ then
$succ(a)=succ(b)$. This is *not* `succ_inj`!
This is trivial -- we can just rewrite our proof of `a=b`.
But how do we get to that proof? Use the `intro` tactic.
-/

/- Theorem
For all naturals $a$ and $b$, $a=b\implies succ(a)=succ(b)$. 
-/
theorem succ_eq_succ_of_eq {a b : mynat} : a = b → succ(a) = succ(b) :=
begin [nat_num_game]
  intro h,
  rw h,
  refl,
end

end mynat -- hide