/- 

# Advanced proposition world. 

## Level 4: `iff_trans`.

The mathematical statement $P\iff Q$ is equivalent to $(P\implies Q)\land(Q\implies P)$. The `cases`
and `split` tactics work on hypotheses and goals (respectively) of the form `P ↔ Q`. If you need
to write an `↔` arrow you can do so by typing `\iff`, but you shouldn't need to. After an initial
`intro h,` you can type `cases h with hpq hqp` to break `h : P ↔ Q` into its constituent parts.
-/

/- Lemma
If $P$, $Q$ and $R$ are true/false statements, then
$P\iff Q$ and $Q\iff R$ together imply $P\iff R$.
-/
lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro hpq,
  intro hqr,
  cases hpq with hpq hqp,
  cases hqr with hqr hrq,
  split,
  cc,cc,


end
