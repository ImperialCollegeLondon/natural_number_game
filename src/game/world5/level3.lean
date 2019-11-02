import mynat.mul -- * on mynat
import mynat.pow -- ^ on mynat


/- Tactic : intro
If your goal is a function `⊢ P → Q` then `intro` is often the
tactic you will use to proceed. What does it mean to define
a function? Given an arbitrary term of type `P` (or an element
of the set `P` if you think set-theoretically) you need
to come up with a term of type `Q`, so your first step is
to choose `p`, an arbitary 
`intro p,` is Lean's way
of saying "let $p ∈ P$ be arbitrary". `intro p` changes

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
-/

/-
# Function world. 

## Level 3 : `intro`

Let's make a function. Let's define the function on the natural
numbers which sends a natural number $n$ to $3*n^2+2*n+1$. If you delete the
`sorry` you will see that our goal is `mynat → mynat`. A mathematician
might denote this set $\operatorname{Hom}(\mathbb{N},\mathbb{N})$
but computer scientists use notation `X → Y`
to denote the set `\operatorname{Hom}(X,Y)`.
We write $f\in\operatorname{Hom}(X,Y)$, but for them,
`X → Y` is a type, and `f : X → Y` means that `f` is a term
of this type, i.e., a function.

To define a function $X\to Y$ we need to choose an arbitrary
element $x\in X$ and then, perhaps using $x$, make an element of $$Y$$.
The Lean tactic for "let $x\in X$ be arbitrary" is `intro x`.

To solve the goal below, you have to come up with a function from `mynat`
to `mynat`. Start with

`intro n,`

(i.e. "let $n\in\mathbb{N}$ be arbitrary") and then use `exact` and return
the value you want. For example

`exact 3*n^2+2*n+1,`

. This will close the goal. 

TODO -- a mathematician *definitely* thinks that this is a *definition*,
not a lemma.
-/ 


/- Lemma
There's a function $\mathbb{N}\to\mathbb{N}$. 
-/
lemma level3 : mynat → mynat :=
begin
  intro n,
  exact n,



end



-- todo 
-- apply