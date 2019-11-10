/-
# Proposition world. 

## Level 9: a big maze. 

Lean's "congruence closure" tactic `cc` is good at mazes. Perhaps I should have
mentioned it earlier.
-/

/- Lemma : no-side-bar
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
Now move onto advanced proposition world, where you will see
how to prove goals such as `P ∧ Q` ($P$ and $Q$), `P ∨ Q` ($P$ or $Q$),
`P ↔ Q` ($P\iff Q$), `∃ x, P(x)` (there exists $x$ such that $P(x)$ is true) and so on.
You will need to learn five more tactics: `cases`, `split`, `left`, `right` and `use`,
but they are all straightforward, and furthermore they are the last tactics you
need to know in order to complete all the levels of the Natural Number Game, including all 30
levels of Inequality World. 
-/
