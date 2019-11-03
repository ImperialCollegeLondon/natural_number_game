/- Tactic : have
If you want to name a term of some type (because you want it
in your local context for some reason), and if you have the
formula for the term, you can use `have` to give the term a name. 

## Example

If the local context contains
```
f : P → Q
p : P
```

then the tactic `have q := f(p),` will add `q` to our local context,
leaving it like this:

```
f : P → Q
p : P
q : Q
```

If you think about it, you don't ever really need `q`, because whenever you
think you need it you coudl just use `f(p)` instead. But it's good that
we can introduce convenient notation like this.
-/

/-
# Function world. 

## Level 3 : `have`.

Say you have a whole bunch of sets and functions between them,
and your goal is to build a certain element of a certain set.
If it helps, you can build intermediate elements of other sets
along the way, using the `have` command. `have` is the Lean analogue
of saying "let's define an element $q\in Q$ by..." in the middle of a calculation.
It is often not logically necessary, but on the other hand
it is very convenient, for example it can save on notation, or
it can break proofs or calculations up into smaller steps.

In the level below, we have an element of $P$ and we want an element
of $U$; during the proof we will make several intermediate elements
of some of the other sets involved. The diagram of sets and
functions looks like this pictorially:

TODO -- better diagram?

```
       h      i
    P ---→ Q ---→ R
           |
           |j
       k   ↓   l
    S ---→ T ---→ U
```

and so it's clear how to make the element of $U$ from the element of $P$.
Indeed, we could solve this level in one move by typing

`exact l(j(h(P))),`

But let us instead stroll more lazily through the level.
We can start by using the `have` tactic to make an element of $Q$:

`have q := h(p),`

and then we note that $j(q)$ is an element of $T$:

`have t := j(q),`

and we could even define $u$ to be $l(t)$:

`have u := l(t),`

and then finish the level with `exact u,`. 
-/

/- Lemma
We can solve a maze.
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
  have q := h(p),
  have t := j(q),
  have u := l(t),
  exact u,


end

/-
If you solved the level using `have` then just before the `exact` line,
the local context is in something like the following mess:

```
P Q R S T U : Type,
p : P,
h : P → Q,
i : Q → R,
j : Q → T,
k : S → T,
l : T → U,
q : Q,
t : T,
u : U
⊢ U
```

It was already bad enough to start with, and we added three more
terms to it. In level 4 we will learn about the `apply` tactic
which solves the level using another technique, without leaving
so much junk behind.
-/