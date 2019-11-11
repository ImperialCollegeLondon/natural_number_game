/- 

# Advanced proposition world. 

## Level 3: and_trans.
-/

/- Lemma
If $P$, $Q$ and $R$ are true/false statements, then $P\land Q$ and
$Q\land R$ together imply $P\land R$.
-/
lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R :=
begin
  intro hpq,
  intro hqr,
  cases hpq with p q,
  cases hqr with q' r,
  split,
  assumption,
  assumption,


end
