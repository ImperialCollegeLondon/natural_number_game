/- 

# Advanced proposition world. 

## Level 3: and_trans.
-/

/- Lemma
If $P$, $Q$ and $R$ are true/false statements, then `P ∧ Q` and `Q ∧ R` together imply `P ∧ R`.
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
