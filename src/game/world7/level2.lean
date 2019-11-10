/- 

# Advanced proposition world. 

## Level 2: the `cases` tactic.

If `P ∧ Q` is in the goal, then we can make progress with `split`.
If `P ∧ Q` is a hypothesis then the `cases` tactic will enables
us to extract proofs of `P` and `Q` from this hypothesis.

The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is,
symmetry of the "and" relation. Starting with

`intro h,`

is the obvious first move, because the goal is an implication.
Now `h : P ∧ Q` is a hypothesis, and

`cases h with p q,`

will change `h`, the proof of `P ∧ Q` to two proofs `p : P`
and `q : Q`. From there, `split` and `exact` will get you home.
-/

/- Lemma
If $P$ and $Q$ are true/false statements, then $P\land Q\implies Q\land P$. 
-/
lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with p q,
  split,
  exact q,
  exact p,


end 

/- Tactic : cases

## Summary:

If `h : P ∧ Q` or `h : P ↔ Q` then `cases h with h1 h2` will remove `h`
from the local context and replace it with the "ingredients" of `h`,
i.e. `h1 : P` and `h2 : Q`, or `h1 : P → Q` and `h2 : Q → P`. Also
works with `h : P ∨ Q` and `n : mynat`. 

## Details

***
-/