/- Tactic : apply
If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function which turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`
goal is a function `⊢ P → Q` then `intro` is often the
tactic you will use to proceed. What does it mean to define
a function? Given an arbitrary term of type `P` (or an element
of the set `P` if you think set-theoretically) you need
to come up with a term of type `Q`, so your first step is
to choose `p`, an arbitary 
`intro p,` is Lean's way
of sayin
-/
import tactic.tauto
example (P Q R : Type) : (Q → R) → (P → Q) → (P → R) :=
begin
  intro h1,
  apply function.comp,
  assumption,
end

-- TODO -- make human-ready
example (P Q R F : Type) : P → (P → empty) → empty := by tauto
example (P Q R F : Type) : ((P → empty) → empty) → P :=
begin
  intro h,
  /-
  P Q R F : Type,
  h : (P → empty) → empty
  ⊢ P
  -/
  -- now what?
  sorry
end

/-
# Function world. 

## Level 4 : `apply`


-/
