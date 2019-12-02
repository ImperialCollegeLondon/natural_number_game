import mynat.definition -- hide
import mynat.add -- hide
import game.world8.level1 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 2: `succ_succ_inj`.
-/

/-
In the below theorem, we need to apply `succ_inj` twice. Once to prove
$succ(succ(a))=succ(succ(b))\implies succ(a)=succ(b)$, and then again
to prove $succ(a)=succ(b)\implies a=b$. However `succ(a)=succ(b)` is
nowhere to be found, it's neither an assumption or a goal when we start
this level. You can make it with `have` or you can use `apply`.
-/
/- Theorem
For all naturals $a$ and $b$, if we assume $succ(succ(a))=succ(succ(b))$, then we can
deduce $a=b$. 
-/
theorem succ_succ_inj {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin [nat_num_game]
    have h2 : succ(a)=succ(b),
      exact succ_inj(h),
    exact succ_inj(h2),



end

/-
## Sample solutions to this level. 

Make sure you understand them all. And remember that `rw` is no use to us here,
`rw` works only with equalities or `↔` statements, not implications or functions.

-/
example {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin
  apply succ_inj,
  apply succ_inj,
  exact h
end 

example {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin
  apply succ_inj,
  exact succ_inj(h),
end 

example {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin
  exact succ_inj(succ_inj(h)),
end 

end mynat -- hide