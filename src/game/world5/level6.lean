/-
# Function world. 

## Level 6 : `(P → (Q → R)) → ((P → Q) → (P → R))`.

You can solve this level completely just using `intro`, `apply` and `exact`,
but if you want to argue forwards instead of backwards then don't forget
that you can do things like `let j : Q → R := f p` if `f : P → (Q → R)`
and `p : P`. I recommend that you start with `intro f` rather than `intro p`
because even though the goal starts `P → ...`, the brackets mean that
the goal is not a function from `P` to anything, it's a function from
`P → (Q → R)` to something. If you do start with `intro f`, and your goal is `⊢ R` later on,
try `apply f` and then try and figure out what just happened. This is a little
`apply` easter egg. Why is it mathematically valid?
-/

/- Lemma
Whatever the sets $P$ and $Q$ and $R$ are, we can always
make an element of $\operatorname{Hom}(\operatorname{Hom}(P,\operatorname{Hom}(Q,R)),
\operatorname{Hom}(\operatorname{Hom}(P,Q),\operatorname{Hom}(P,R)))$.
-/
example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
  intro f,
  intro h,
  intro p,
  let j : Q → R := f p,
  apply j,
  apply h,
  exact p,


end
