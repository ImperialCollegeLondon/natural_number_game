/- Tactic : let
If you want to name a term of some type (because you want it
in your local context for some reason), and if you have the
formula for the term, you can use `let` to give the term a name. 

## Example

If the local context contains
```
f : P → Q
p : P
```

then the tactic `let q := f(p),` will add `q` to our local context,
leaving it like this:

```
f : P → Q
p : P
q : Q := f p
```
Note that Lean leaves the definition of `q` in the local context
as well, to remind us where it came from.
Because `q` is *defined to be `f(p)`*, when Lean sees `q` later on
it will just imagine it is seeing `f(p)`. Note in particular
that `let` is never logically necessary in a proof, it is just
there for convenience.
-/

/-
# Function world. 

## Level 3 : `let`.

Say you have a whole bunch of sets and functions between them,
and your goal is to build a certain element of a certain set.
If it helps, you can build intermediate elements of other sets
along the way, using the `let` command. `let` is the Lean analogue
of saying "let's define $q$ to be $f(p)$" in the middle of a proof.
It is often not logically necessary, but on the other hand
it is very convenient, for example it can save on notation, or
it can break proofs up into smaller steps.

In the level below, we have an element of $P$ and we want an element
of $U$; during the proof we will make several intermediate elements
of some of the other sets involved. The diagram of sets and
functions looks like this pictorially:

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
We can start by using the `let` tactic to make an element of $Q$:

`let q := h(p),`

and then we note that $j(q)$ is an element of $T$:

`let t := j(q),`

and we could even define $u$ to be $l(t)$:

`let u := l(t),`

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
  let q := h(p),
  let t := j(q),
  let u := l(t),
  exact u,


end

/-
If you solved the level using `let` then at the end of it,
the local context is in the following mess:

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
which solves the level in the same sort of way without leaving
so much junk behind.
-/