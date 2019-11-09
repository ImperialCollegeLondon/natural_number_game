import mynat.add -- + on mynat
import mynat.mul -- * on mynat



/- Tactic : intro

## Summary:

`intro p` will make progress if the goal is of the form `P → Q`.

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. What does it mean to define
a function? Given an arbitrary term of type `P` (or an element
of the set `P` if you think set-theoretically) you need
to come up with a term of type `Q`, so your first step is
to choose `p`, an arbitary element of `P`. 

`intro p,` is Lean's way of saying "let $p\in P$ be arbitrary".
The tactic `intro p` changes

```
⊢ P → Q
```

into

```
p : P
⊢ Q
```

So `p` is an arbitrary element of `P` about which nothing is known,
and our task is to come up with an element of `Q` (which can of
course depend on `p`).

Note that the opposite of `intro` is `revert`; given a tactic
state

```
p : P
⊢ Q
```

as above, the tactic `revert p` takes us back to `⊢ P → Q`. 

## Example (propositions)
-/

/-
# Function world. 

## Level 2: the `intro` tactic.

Let's make a function. Let's define the function on the natural
numbers which sends a natural number $n$ to $3n+2$. If you delete the
`sorry` you will see that our goal is `mynat → mynat`. A mathematician
might denote this set with some exotic name such as
$\operatorname{Hom}(\mathbb{N},\mathbb{N})$,
but computer scientists use notation `X → Y` to denote the set of
functions from `X` to `Y` and this name definitely has its merits.
In type theory, `X → Y` is a type (the type of all functions from $X$ to $Y$),
and `f : X → Y` means that `f` is a term
of this type, i.e., $f$ is a function from $X$ to $Y$.

To define a function $X\to Y$ we need to choose an arbitrary
element $x\in X$ and then, perhaps using $x$, make an element of $Y$.
The Lean tactic for "let $x\in X$ be arbitrary" is `intro x`.

## Rule of thumb: 

If your goal is `P → Q` then `intro p` will make progress.

To solve the goal below, you have to come up with a function from `mynat`
to `mynat`. Start with

`intro n,`

(i.e. "let $n\in\mathbb{N}$ be arbitrary") and note that our
local context now looks like this:

```
n : mynat
⊢ mynat
```

Our job now is to construct a natural number, which is
allowed to depend on $n$. We can do this using `exact` and
writing a formula for the function we want to define. For example
we imported addition and multiplication at the top of this file,
so 

`exact 3*n+2,`

will close the goal, ultimately defining the function $f(n)=3n+2$.

-/ 


/- Definition
We define a function from mynat to mynat.
-/
example : mynat → mynat :=
begin [less_leaky]
  intro n,
  exact 3*n+2,



end
-- TODO this is a function