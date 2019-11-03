-- World name : Proposition world
/- 

# Proposition world. 

A Proposition is a true/false statement, like `2 + 2 = 4` or `2 + 2 = 5`.
Just like we can have concrete sets in Lean like `mynat`, and abstract
sets called things like `X`, we can also have concrete propositions like
`2 + 2 = 5` and abstract propositions called things like `P`. 

Mathematicians are very good at conflating a theorem with its proof.
They might say "now use theorem 12 and we're done". What they really
mean is "now use the proof of theorem 12..." (i.e. the fact that we proved
it already). Particularly problematic is the fact that mathematicians
use the word Proposition to mean "a relatively straightforward statement
which is true" and computer scientists use it to mean "a statement of
arbitrary complexity, which might be true or false". Computer scientists
are far more careful about distinguishing the two concepts: a proposition
(for example: `∀ x : mynat, x + 0 = x`) and its proof (for example `add_zero`).
In this world you will see the local context in the following kind of state:

```
P : Prop
p : P
```

Here `P` is the statement, and `p` is its proof. It's like `P`
being the set and `p` being the element. In fact computer scientists
sometimes think about the following analogy: propositions are like sets,
and proofs are like their elements. 

## What's going on in this world? 

We're going to learn about manipulating propositions and proofs.
Fortunately, we don't need to learn a bunch of new tactics -- the
ones we just learnt (`intro`, `exact`, `apply`) will be perfect.

The levels in proposition world are "back to normal", we're proving
theorems, not constructing elements of sets. Or are we?

If you delete the sorry below then your local context will look like this:

```
P Q : Prop,
p : P,
h : P → Q
⊢ Q
```

In this situation, we have true/false statements $P$ and $Q$,
a proof $p$ of $P$, and $h$ is the hypothesis that $P\implies Q$.
Our goal is to construct a proof of $Q$. It's clear what to do
*mathematically* to solve this goal -- we can deduce $Q$
by applying the hypothesis $h:P\implies Q$ to
the proof $p$ of $P$. But how to do it in Lean?

Adopting a point of view wholly unfamiliar to mathematicians,
Lean interprets the hypothesis $h$ as a function from proofs
of $P$ to proofs of $Q$, so the rather surprising approach

`exact h(p),`

works to close the goal. Note that `exact h(P),` won't work;
$P$ is not proof of $P$, it's $p$ that is a proof of $P$. 

In Lean, Propositions are types, like sets.

## Level 1 -- `exact`
-/

/- Lemma : no-side-bar
If $P$ is true, and $P\implies Q$, then $Q$ is true.
-/
lemma level1 (P Q : Prop) (p : P) (h : P → Q) : Q :=
begin
exact h(p),



end 

