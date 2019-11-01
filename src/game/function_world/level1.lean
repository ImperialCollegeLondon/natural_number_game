-- World name : Function world
/- 
If you have beaten Addition World in this game, then you have got
quite good at manipulating equalities in Lean using the `rw` tactic.
But there are plenty of levels later on which will require you
to manipulate functions, and `rw` is not the tool for you here.

To manipulate functions effectively, we need to learn about a new collection
of tactics -- `intro`, `apply`, `exact` and `have` (TODO -- put them
in the order I introduce them), specially designed for dealing with
functions. Of course we are ultimately interested in using these
tactics to prove theorems about the natural numbers -- but in this
world there is little point in working with specific sets like `mynat`,
everything works for general sets.

So our notation for this level is: $P$, $Q$, $R$ and so on denote general
sets, and let $h$, $j$, $k$ and so on denote general functions between
them. What we will learn in this world is how to use the Lean theorem
prover to move elements around between these sets using the functions
we are given, and the tactics we will learn. A word of warning -- Lean
works with Types not sets, so `P`, `Q` and `R` will be general types,
and instead of elements of a given set, we'll have terms of a given type.
This is just a language issue, but it does mean that we will write `p : P`
instead of `p ∈ P`. 

The levels in function world aren't theorems like in the natural
number game -- in function world the object of a level is to create
an element of the set in the goal. For example if your local
context (the top right hand box) looked like this:

```
P Q : Type,
p : P,
h : P → Q
⊢ Q
```

then this means that we have sets $P$ and $Q$, an element $p$ of $P$,
a function $h$ from $P$ to $Q$, and our goal is to construct an
element of $Q$. It's clear what to do to solve this goal -- we can
make an element of $Q$ by applying the function $Q$ to
the element $p$. There are at least two ways to do it, and here I'll explain
how to use the `exact` tactic to solve this goal.

## The `exact` tactic. 

If you can explicitly see how to make an element of of your goal type,
i.e. you have a formula for it, then you can just write `exact <formula>` 
and this will close the goal. 

### Example

If your local context looks like this

```
P Q : Type,
p : P,
h : P → Q
⊢ Q
```

then $h(p)$ is an element of $Q$ so you can just write

`exact h(p),`

to close the goal. 

## Level 1 -- `exact`
-/

/- Lemma
Given an element of $P$ and a function from $P$ to $Q$,
you can get an element of $Q$.
-/
lemma level1 (P Q : Type) (p : P) (h : P → Q) : Q :=
begin
exact h(p),



end 

/- Tactic : exact

If the local context is like this: 

```
1 goal
P Q R : Type,
p : P,
h : P → Q,
j : Q → R
⊢ R
```

and you can see how to make the element of $R$, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h(p)),`



-/

