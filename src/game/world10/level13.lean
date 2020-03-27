import game.world10.level12 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 13: `not_succ_le_self`

Turns out that `¬ P` is *by definition* `P → false`, so you can just
start this one with `intro h` if you like. 

## Pro tip:

```
  conv begin
    to_lhs,
    rw hc,
  end,
```

is an incantation which rewrites `hc` only on the left hand side of the goal.
Look carefully at the commas.
-/

/- Lemma
For all naturals $a$, $\operatorname{succ}(a)$ is not at most $a$.
-/
theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=
begin [nat_num_game]
  intro h,
  induction a with d hd,
    cases h with c hc,
    rw succ_add at hc,
    exact zero_ne_succ _ hc,
  apply hd,
  cases h with c hc,
  use c,
  apply succ_inj,
  conv begin
    to_lhs,
    rw hc,
  end,
  rw ←succ_add,
  rw ←hc,
  refl,


end

end mynat -- hide
