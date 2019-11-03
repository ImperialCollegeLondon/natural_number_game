/-
# Function world. 

## Level 9 : a big maze. 

I asked around on Zulip and apparently there is not a tactic for this, perhaps because
this level is rather artificial. In world 6 we will see a variant of this example
which can be solved by a tactic. It would be an interesting project to make a tactic
which could solve this sort of level in Lean.
-/

/- Lemma : no-side-bar
There is a way through the following maze.
-/
example (A B C D E F G H I J K L : Type)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L :=
begin
  intro a, apply f15, apply f11, apply f9, apply f8, apply f5, apply f2, apply f1, assumption,







end

/-
Next it's Proposition world and I'm hoping that the tactics we've just learnt will be enough
to get us through it.
-/
