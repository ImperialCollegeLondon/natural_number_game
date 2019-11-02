/- Tactic : apply
If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function which turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`. A mathematician might say: "we need
to construct an element of $Q$, but we have a function $h:P\to Q$
so it suffices to construct an element of $P$". Or alternatively
"we need to prove $Q$, but we have a proof $h$ that $P\implies Q$
so it suffices to prove $P$".

-/

/-

# Function world. 

## Level 4 : `apply`.

Let's do the same level again:

```
       h      i
    P ---→ Q ---→ R
           |
           |j
       k   ↓   l
    S ---→ T ---→ U
```

We are given $p \in P$ and our goal is to find an element of $U$, or
in other words to find a path through the maze that links $P$ to $Q$.
In level 3 we solved this by using `let`s to move forward, from $P$
to $Q$ to $T$ to $U$. Using the `apply` tactic we can instead construct
the path backwards, moving from $U$ to $T$ to $Q$ to $P$.

Our goal is to construct an element of the set $U$. But $l:T\to U$ is
a function, so it would suffice to construct an element of $T$. Tell
Lean this by starting the proof below with

`apply l,`

and notice that our assumptions don't change but *the goal changes*
from `⊢ U` to `⊢ T`. 

Keep `apply`ing functions until your goal is `P`. Now solve this goal
with `exact p`. Note: you will need to learn the difference between
`exact p` (which works) and `exact P` (which doesn't, because $P$ is
not an element of $P$).
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
  apply l,
  apply j,
  apply h,
  exact p,



end