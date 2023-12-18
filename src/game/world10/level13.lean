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
Look carefully at the commas. You don't need to use `conv` to solve this,
but it's a helpful trick when `rw` is rewriting too much.
-/

/- Lemma
For all naturals $a$, $\operatorname{succ}(a)$ is not at most $a$.
-/
theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=
begin [nat_num_game]
  intro h,
  have f := le_succ_self a,
  have g := le_antisymm a _ f h,
  apply ne_succ_self a,
  exact g,




end

end mynat -- hide

-- thanks to Filip Szczepański for this proof (nicer than the original; I was doing -- hide
-- induction a before cases h) -- hide
