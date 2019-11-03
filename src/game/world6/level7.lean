/-
# Function world. 

## Level 8 : `(P → Q) → ((Q → R) → (P → R))` 

If you start with `intro hpq` and then `intro `hqr`
the dust will clear a bit and the level will look like this:
```
P Q R : Prop,
hpq : P → Q,
hqr : Q → R
⊢ P → R
```
So this level is really about showing transitivity of $\implies$,
if you like that sort of language.
-/

/- Lemma : no-side-bar
From $P\implies Q$ and $Q\implies R$ we can deduce $P\implies R$.
-/
example (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) :=
begin
  intros hpq hqr,
  intro p,
  apply hqr,
  apply hpq,
  assumption
  

end
