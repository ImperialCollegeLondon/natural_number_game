import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level8 -- hide
namespace mynat -- hide

/- Axiom : zero_ne_succ (a : mynat) :
0 ≠ succ(a)
-/

/-

# Advanced Addition World

## Level 9: `succ_ne_zero`

Levels 9 to 13 introduce the last axiom of Peano, namely
that $0\not=\operatorname{succ}(a)$. The proof of this is called `zero_ne_succ a`. 

`zero_ne_succ (a : mynat) : 0 ≠ succ(a)`

The `symmetry` tactic will turn any goal of the form `R x y` into `R y x`,
if `R` is a symmetric binary relation (for example `=` or `≠`).
In particular, you can prove `succ_ne_zero` below by first using
`symmetry` and then `exact zero_ne_succ a`.
-/

/- Theorem
Zero is not the successor of any natural number.
-/
theorem succ_ne_zero (a : mynat) : succ a ≠ 0 := 
begin [less_leaky]
  symmetry,
  exact zero_ne_succ a,


end

end mynat
