import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level8 -- hide
namespace mynat -- hide

/- Axiom : zero_ne_succ (a : mynat) :
0 ≠ succ(a)
-/

/- Tactic : symmetry

## Summary

`symmetry` turns goals of the form `⊢ A = B` to `⊢ B = A`.
Also works with `≠`. Also works on hypotheses: if `h : a ≠ b`
then `symmetry at h` gives `h : b ≠ a`.

## Details

`symmetry` works on both goals and hypotheses. By default it
works on the goal. It will turn a goal of the form `⊢ A = B`
to `⊢ B = A`. More generally it will work with any symmetric
binary relation (for example `≠`, or more generally any
binary relation whose proof of symmetry has been tagged
with the `symm` attribute).

To get `symmetry` working on a hypothesis, use `symmetry at h`.

## Examples

If the tactic state is
```
h : a = b
⊢ c ≠ d
```

then `symmetry` changes the goal to `⊢ d ≠ c` and
`symmetry at h` changes `h` to `h : b = a`.
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
begin [nat_num_game]
  symmetry,
  exact zero_ne_succ a,


end

end mynat
