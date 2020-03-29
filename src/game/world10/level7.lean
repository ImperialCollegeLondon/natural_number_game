import game.world10.level6 -- hide
namespace mynat -- hide
/-
# Inequality world 

## Level 7: `le_zero`

We proved `add_right_eq_zero` back in advanced addition world.
Note that you can do things like `have h2 := add_right_eq_zero _ _ h1`
if `h1 : a + c = 0`.
-/

/- Lemma
For all naturals $a$, if $a\le 0$ then $a = 0$.
-/
lemma le_zero (a : mynat) (h : a ≤ 0) : a = 0 :=
begin [nat_num_game]
  cases h with c hc,
  symmetry at hc,
  exact add_right_eq_zero hc,


end

end mynat -- hide
