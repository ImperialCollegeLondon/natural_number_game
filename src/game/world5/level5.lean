/-
# Function world. 

## Level 5 : `P → (Q → P)`.

In this level, our goal is to construct a function, like in level 2.

```
⊢ P → (Q → P)
```

So $P$ and $Q$ are sets, and our goal is to construct a function
which takes an element of $P$ and outputs a function from $Q$ to $P$.
We don't know anything at all about the sets $P$ and $Q$, so initially
this seems like a bit of a tall order. But let's give it a go. Delete
the `sorry` and let's think about how to proceed.

Our goal is `P → X` for some set $X=\operatorname{Hom}(Q,P)$, and if our
goal is to construct a function then we almost always want to use the
`intro` tactic from world 2, Lean's version of "let $p\in P$ be arbitrary."
So let's start with

`intro p,`

and we then find ourselves in this state:

```
P Q : Type,
p : P
⊢ Q → P
```

We now have an arbitrary element $p\in P$ and we are supposed to be constructing
a function $Q\to P$. Well, how about the constant function, which sends everything to $p$?
This will work. So let $q\in Q$ be arbitrary:

`intro q,`

and then let's output `p`.

`exact p,`
-/

/- Lemma : no-side-bar
Whatever sets $P$ and $Q$ are, we can always
make an element of $\operatorname{Hom}(P,\operatorname{Hom}(Q,P))$.
-/
example (P Q : Type) : P → (Q → P) :=
begin
  intro p,
  intro q,
  exact p,


end

/-
A mathematician would treat the set `P → (Q → P)` as the same as the set `P × Q → P`,
because to give an element of either function space is just to give a rule which takes
an element of $P$ and an element of $Q$, and returns an element of $P$. Thinking of the
goal as a function from `P × Q` to `P` we realise that it's just projection onto the first
factor.

## Did you notice?

I wrote `P → (Q → P)` but Lean just writes `P → Q → P`. This is because
computer scientists adopt the convention that `→` is *right associative*,
which is a fancy way of saying "when we write `P → Q → R`, we mean `P → (Q → R)`."
Mathematicians use right associativity as a convention for powers: if
a mathematician says $10^{10^{10}}$ they don't mean $(10^{10})^{10}=10^{100}$, they
mean $10^{(10^{10})}$. So `10 ^ 10 ^ 10` in Lean means `10 ^ (10 ^ 10)` and not `(10 ^ 10) ^ 10`.
However they use left associativity as a convention for subtraction: if
a mathematician writes $6 - 2 - 1$ they mean $(6 - 2) - 1$ and not $6 - (2 - 1)$.
-/