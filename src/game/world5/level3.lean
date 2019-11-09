/- Tactic : have

## Summary

`have h : P,` will create a new goal of creating a term of type `P`,
and will add `h : P` to the hypotheses for the goal you were working on.

## Details

If you want to name a term of some type (because you want it
in your local context for some reason), and if you have the
formula for the term, you can use `have` to give the term a name. 

## Example (`have q := ...` or `have q : Q := ...`)

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

## Example (`have q : Q,`)

A variant of this tactic can be used where you just declare the
type of the term you want to have, finish the tactic statement with
a comma and no `:=`, and then Lean just adds it as a new goal.
The number of goals goes up by one if you use `have` like this.

For example if the local context is
```
P Q R : Prop/Type,
f : P → Q,
g : Q → R,
p : P
⊢ R
```

then after `have q : Q,`, there will be the new goal
```
f : P → Q,
g : Q → R,
p : P,
⊢ Q
```

and your original goal will have `q : Q` added to the list
of hypotheses.
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

![diagram](https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game_images/function_diag.jpg)

and so it's clear how to make the element of $U$ from the element of $P$.
Indeed, we could solve this level in one move by typing

`exact l(j(h(P))),`

But let us instead stroll more lazily through the level.
We can start by using the `have` tactic to make an element of $Q$:

`have q := h(p),`

and then we note that $j(q)$ is an element of $T$

`have t : T := j(q),`

(notice how on this occasion we explicitly told Lean what set we thought $t$ was in, with
that `: T` thing before the `:=`) and we could even define $u$ to be $l(t)$:

`have u : U := l(t),`

and then finish the level with

`exact u,`

. 
-/

/- Lemma : no-side-bar
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
  have t : T := j(q),
  have u : U := l(t),
  exact u,


end

/-
If you solved the level using `have`, then click on the last line of your proof
(you do know you can move your cursor around with the arrow keys
and explore your proof, right?) and note that the local context at that point
is in something like the following mess:

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