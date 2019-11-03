-- World name : Function world
/- 

# Function world. 

If you have beaten Addition World, then you have got
quite good at manipulating equalities in Lean using the `rw` tactic.
But there are plenty of levels later on which will require you
to manipulate functions, and `rw` is not the tool for you here.

To manipulate functions effectively, we need to learn about a new collection
of tactics, namely `exact`, `intro`, `have` and `apply`. These tactics
are specially designed for dealing with functions. Of course we are
ultimately interested in using these tactics to prove theorems
about the natural numbers -- but in this
world there is little point in working with specific sets like `mynat`,
everything works for general sets.

So our notation for this level is: $P$, $Q$, $R$ and so on denote general sets,
and $h$, $j$, $k$ and so on denote general
functions between them. What we will learn in this world is how to use Lean
to move elements around between these sets using the functions
we are given, and the tactics we will learn. A word of warning -- 
even though there's no harm at all in thinking of $P$ being a set and $p$
being an element, you will not see Lean using the notation $p\in P$, because
internally Lean stores $P$ as a "Type" and $p$ as a "term", and it uses `p : P`
to mean "$p$ is a term of type $P$", Lean's way of expressing the idea that $p$
is an element of the set $P$. 

## A new kind of goal.

All through addition and multiplication world, our goals have been theorems,
and it was our job to find the proofs. 
**The levels in function world aren't theorems**. This is the only world where
the levels aren't theorems in fact. In function world the object of a level
is to create an element of the set in the goal. The goal will look like `⊢ X`
with $X$ a set and you get rid of the goal by constructing an element of $X$. 
I don't know if you noticed this, but essentially every goal you solved in
levels 2 to 4 you solved with `refl`. This tactic is no use to us here.
We are going to have to learn a new way of solving goals -- the `exact` tactic.

If you delete the sorry below then your local context will look like this:

```
P Q : Type,
p : P,
h : P → Q
⊢ Q
```

In this situation, we have sets $P$ and $Q$ and an element $p$ of $P$ (written `p : P`
but meaning $p\in P$). We also have a function $h$ from $P$ to $Q$,
and our goal is to construct an
element of the set $Q$. It's clear what to do *mathematically* to solve
this goal -- we can
make an element of $Q$ by applying the function $h$ to
the element $p$. But how to do it in Lean? There are at least two ways,
and here we will learn about one of them, namely the method which
uses the `exact` tactic to explain our mathematical argument to Lean.

## The `exact` tactic. 

If you can explicitly see how to make an element of of your goal set,
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

## Important note

Note that `exact h(P),` won't work (with a capital $P$);
this is a common error I see from beginners. 
$P$ is not an element of $P$, it's $p$ that is an element of $P$. 

## Level 1 -- `exact`
-/

/- Lemma : no-side-bar
Given an element of $P$ and a function from $P$ to $Q$,
you can get an element of $Q$.
-/
lemma level1 (P Q : Type) (p : P) (h : P → Q) : Q :=
begin
exact h(p),



end 

/- Tactic : exact

Say $P$, $Q$ and $R$ are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this: 

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h(p)),`

because $j(h(p))$ is easily checked to be a term of type $R$
(i.e., an element of the set $R$, or a proof of the proposition $R$).

-/

