/-
# Proposition world. 

## Level 2 : `intro`.

Let's prove an implication. Let $P$ be a true/false statement,
and let's prove that $P\implies P$. If you delete the
`sorry` you will see that our goal is `P → P`. Constructing a term
of type `P → P` (which is what solving this goal *means*) in this
case amounts to proving that $P\implies P$, and computer scientists
think of this as coming up with a function which sends proofs of $P$
to proofs of $P$.

To define an implication $P\implies Q$ we need to choose an arbitrary
proof $p : P$ of $P$ and then, perhaps using $p$, construct a proof
of $Q$.  The Lean way to say "let's assume $P$ is true" is `intro p`,
i.e., "let's assume we have a proof of $P$". Those of you who know
something about the subtle differences between truth and provability
discovered by Goedel -- I would strongly advise that you completely
forget about them for the moment because this issue is not relevant
here. $p$ doesn't have to be thought of as a proof of $P$, it can be
interpreted as some sort of more abstract "evidence for the truth of $P$"
or "witness to the truth of $P$" if you like. This is however philosophy
rather than mathematics, and it's easiest to just think of $p$ as a proof of $P$.

## Rule of thumb: 

If your goal is to prove `P → Q` (i.e. that $P\implies Q$)
then `intro p`, meaning "assume $P$ is true", will make progress.

To solve the goal below, you have to come up with a function from
`P` (thought of as the set of proofs of $P$!) to itself. Start with

`intro p,`

(i.e. "let $p$ be a proof of $P$") and note that our
local context now looks like this:

```
P : Prop,
p : P
⊢ P
```

Our job now is to construct a proof of $P$. But $p$ is a proof of $P$.
So

`exact p,`

will close the goal. Note that `exact P` will not work -- don't
confuse a true/false statement (which could be false!) with a proof.
We will stick with the convention of capital letters for propositions
and small letters for proofs.
-/ 


/- Lemma : no-side-bar
If $P$ is a proposition then $P\implies P$.
-/
lemma level2 (P : Prop) : P → P :=
begin
  intro p,
  exact p,



end
