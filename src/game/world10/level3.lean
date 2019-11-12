import game.world10.level1 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 3: le_succ_of_le

We have seen how the `use` tactic makes progress on goals of the form `⊢ ∃ c, ...`.
But what do we do when we have a *hypothesis* of the form `∃ c, ...`?

-/

/- Lemma
For all naturals $a$, $b$, if $a\leq b$ then $a\leq \operatorname{succ}(b)$. 
-/
theorem le_succ {a b : mynat} (h : a ≤ b) : a ≤ (succ b) :=
begin [less_leaky]
  rw le_def at h ⊢,
  cases h with c hc,
  use (succ c),
  rw hc,
  rw add_succ,
  refl,


end

/-
Did you use `succ c` or `c + 1` or `1 + c`? Those numbers are all
equal, right? So it doesn't matter which one you use, right?
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
