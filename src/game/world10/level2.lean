import game.world10.level1 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

Here's a nice easy one.

## Level 2: le_refl 
-/
/- Lemma : 
The $\le$ relation is reflexive. In other words, if $x$ is a natural number,
then $x\le x$.
-/
lemma le_refl (x : mynat) : x ≤ x :=
begin [less_leaky]
  use 0,
  rw add_zero,
  refl,


end 
/-
## Upgrading the `refl` tactic 

Now with the following incantation (NB thanks to master wizard Reid Barton
for correcting my spell) :
-/
attribute [refl] mynat.le_refl
/-
...we now find that the `refl` tactic will close all goals
of the form `a ≤ a` as well as all goals of the form `a = a`.
-/
example : (0 : mynat) ≤ 0 := begin
  refl
end

/-
## Pro tip

Did you skip `rw le_def` in your proof of `le_refl` above?
Instead of `rw add_zero` or `ring` at the end there,
what happens if you just try `refl`? The *definition* of `x + 0` is `x`,
so you don't need to `rw add_zero` either!

The same remarks are true of
`add_succ`, `mul_zero`, `mul_succ`, `pow_zero` and `pow_succ`. All of those
theorems are true *by definition*. The same is *not* true however of `zero_add`; 
the theorem `0 + x = x` was proved by induction on `x`,
and in particular it is not true by *definition*.

Definitional equality is of great importance
to computer scientists, but mathematicians are much more fluid with their idea
of a definition -- a concept can simultaneously have three equivalent definitions
in a maths talk, as long as they're all logically equivalent. In Lean, a definition
is *one thing*, and definitional equality is a subtle concept which depends on
exactly which definition you chose. `add_comm` is certainly not true by definition,
which means that if we had decided to define `a ≤ b` by `∃ c, b = c + a` (rather
than `a + c`) all the same theorems would be true, but `refl` would work in
different places. `refl` closes a goal of the form `X = Y` if `X` and `Y` are
definitionally equal.
-/
end mynat -- hide
