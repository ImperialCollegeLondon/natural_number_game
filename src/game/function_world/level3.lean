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
state as above, `revert p` takes us back to `⊢ P → Q`. 
-/

/-
# Function world. 

## Level 3 : `intro`

Let's make a constant function. Say $P$ and $Q$ are types,
and `q : Q` is a term of type `Q` (i.e. a element of the set $Q$). 
Let's build the function from $P$ to $Q$ which sends everything
to $q$. 
-/ 

/- Lemma
If $q\in Q$ then we can build a constant function $P\to Q$ sending
every element of $P$ to $q$. 
-/
lemma level3 (P Q : Type)
(q : Q)
: P → Q :=
begin
sorry 



end

-- todo 
-- apply, intro