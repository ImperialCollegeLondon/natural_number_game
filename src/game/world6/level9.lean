/-
# Proposition world. 

## Level 9 : a big maze. 

Lean's "congruence closure" tactic `cc` is good at mazes. Perhaps I should have
mentioned it earlier.
-/

/- Lemma
There is a way through the following maze.
-/
example (A B C D E F G H I J K L : Prop)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L :=
begin
  cc,
end

/-
Still to come in proposition world: `∧`! `∨`! `↔`! `∃`! And
the tactics `cases`, `split`, `left`, `right`, `use`. 
But the good news is that (1) all these tactics are easy and (2)
they will be the last 

-/
