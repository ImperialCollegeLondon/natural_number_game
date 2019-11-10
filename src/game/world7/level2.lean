/- 

# Advanced proposition world. 

## Level 2: the `cases` tactic.

If `P ∧ Q` is in the goal, then we can make progress with `split`.
But what if `P ∧ Q` is a hypothesis? In this case, the `cases` tactic will enable
us to extract proofs of `P` and `Q` from this hypothesis.

The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is,
symmetry of the "and" relation. The obvious first move is

`intro h,`

because the goal is an implication and this tactic is guaranteed
to make progress. Now `h : P ∧ Q` is a hypothesis, and

`cases h with p q,`

will change `h`, the proof of `P ∧ Q`, into two proofs `p : P`
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

`cases` is a tactic which works on hypotheses.
If `h : P ∧ Q` or `h : P ↔ Q` is a hypothesis then `cases h with h1 h2` will remove `h`
from the list of hypotheses and replace it with the "ingredients" of `h`,
i.e. `h1 : P` and `h2 : Q`, or `h1 : P → Q` and `h2 : Q → P`. Also
works with `h : P ∨ Q` and `n : mynat`. 

## Details

How does one prove `P ∧ Q`? The way to do it is to prove `P` and to
prove `Q`. There are hence two ingredients which go into a proof of
`P ∧ Q`, and the `cases` tactic extracts them. 

More precisely, if the local context contains
```
h : P ∧ Q`
```

then after the tactic `cases h with p q,` the local context will
change to
```
p : P,
q : Q
```
and `h` will disappear. 

Similarly `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `cases h with hpq hqp` will delete our assumption `h` and
replace it with
```
hpq : P → Q,
hqp : Q → P
```

Be warned though -- `rw h` works with `h : P ↔ Q` (`rw` works with
`=` and `↔`), whereas you cannot rewrite with an implication.

`cases` also works with hypotheses of the form `P ∨ Q` and even
with `n : mynat`. Here the situation is different however. 
To prove `P ∨ Q` you need to give either a proof of `P` *or* a proof
of `Q`, so if `h : P ∨ Q` then `cases h with p q` will change one goal
into two, one with `p : P` and the other with `q : Q`. Similarly, each
natural is either `0` or `succ(d)` for `d` another natural, so if
`n : mynat` then `cases n with d` also turns one goal into two,
one with `n = 0` and the other with `d : mynat` and `n = succ(d)`.
-/