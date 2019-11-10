/- 

# Advanced proposition world. 

## Level 5: `iff_trans` easter eggs.

Let's try ``iff_trans` again. Try proving it in other ways.

### A trick.

Instead of using `cases` on `h : P ↔ Q` you can just access the proofs of `P → Q` and `Q → P`
directly with `h.1` and `h.2`. So you can solve this level with

```
intros hpq hqr, 
split,
intro p,
apply hqr.1,
...
```

### Another trick

Instead of using `cases` on `h : P ↔ Q`, you can just `rw h`, and this will change all `P`s to `Q`s
in the goal. You can use this to create a much shorter proof.

### Another trick

`cc` works on this sort of goal too.
-/

/- Lemma
If $P$, $Q$ and $R$ are true/false statements, then `P ↔ Q` and `Q ↔ R` together imply `P ↔ R`.
-/
lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hpq hqr,
  split,
  intro p,
  apply hqr.1,

  cases hpq with hpq hqp,
  cases hqr with hqr hrq,
  split,
  cc,cc,


end
