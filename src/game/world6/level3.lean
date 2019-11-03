/-
# Proposition world. 

## Level 3 : `let`.

Say you have a whole bunch of propositions and implications between them,
and your goal is to build a certain proof of a certain proposition.
If it helps, you can build intermediate proofs of other propositions
along the way, using the `let` command. `let` is the Lean analogue
of saying "We now see that $Q$ is true, because here's a proof"
in the middle of a proof.
It is often not logically necessary, but on the other hand
it is very convenient, for example it can save on notation, or
it can break proofs up into smaller steps.

In the level below, we have a proof of $P$ and we want a proof
of $U$; during the proof we will construct proofs of
of some of the other propositions involved. The diagram of
propositions and implications looks like this pictorially:

TODO -- this one should look like $P\implies Q\implies R$ etc.

```
       h      i
    P ---→ Q ---→ R
           |
           |j
       k   ↓   l
    S ---→ T ---→ U
```

and so it's clear how to deduce $U$ from $P$.
Indeed, we could solve this level in one move by typing

`exact l(j(h(P))),`

But let us instead stroll more lazily through the level.
We can start by using the `let` tactic to make a proof of $Q$:

`let q := h(p),`

and then we note that $j(q)$ is a proof of $T$:

`let t := j(q),`

and we could even define $u$ to be $l(t)$:

`let u := l(t),`

and then finish the level with `exact u,`. 
-/

/- Lemma
In the maze of logical implications above, if $P$ is true then so is $U$.
-/
lemma maze (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=
begin
  let q := h(p),
  let t := j(q),
  let u := l(t),
  exact u,


end

/-
If you solved the level using `let` then just before the `exact` line,
the local context is in something like the following mess:

```
P Q R S T U : Type,
p : P,
h : P → Q,
i : Q → R,
j : Q → T,
k : S → T,
l : T → U,
q : Q := h p,
t : T := j q,
u : U := l t
⊢ U
```

It was already bad enough to start with, and we added three more
terms to it. In level 4 we will learn about the `apply` tactic
which solves the level using another technique, without leaving
so much junk behind.
-/