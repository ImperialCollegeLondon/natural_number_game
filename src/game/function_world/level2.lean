/- Tactic : let
If you want to make some term of a type and you have the
formula, you can use `let` to give the term a name. 

## Example

If the local context contains
```
f : P → Q
p : P
```

then the tactic `let q := f(p),` will add `q` to our local context,
and it will also remind us of its definition. Because `q` is
*defined to be `f(p)`*, any arguments at any point in your code which mention
`q` would be true by definition if we just changed `q` to `f(p)`. 
-/

/-
# Function world. 

## Level 2 : `let`

If it helps, you can build intermediate elements along the way,
using the `let` command. It is often not logically necessary,
but on the other hand can often help you to proceed if you're working
step by step. 

In the level below, we have an element of $P$ and we want an element
of $R$; during the proof we will make an intermediate element of $Q$.

-/

/- Lemma
For all naturals $a$, $b$, if $a\leq b$ then $a\leq \operatorname{succ}(b)$. 
-/
lemma level2 (P Q R : Type)
(p : P)
(h : P → Q)
(j : Q → R)
: R :=
begin
--  exact j(h(p)),
  let q := h(p),
  exact j(q),
end

-- todo 
-- apply, intro