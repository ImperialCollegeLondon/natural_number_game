import game.world5.level1 -- hide
namespace mynat -- hide

/-
# World 5 : Inequality world 

## Level 2 : `le_succ`

In this level we will find ourselves with a *hypothesis* of the form `h : ∃ c, P`
where `P` is some
proposition (which probably depends on `c`). To extract `c` from `h` you
can use the `cases` tactic. If `h : ∃ c, P` is as above, then
`cases h with c hc` will create your term `c` as well as creating a proof `hc` of `P`,
i.e., `hc` is the proof that `c` satisfies `P`.

For example, if we have
```
h : ∃ c : mynat, c + c = 12
```

then 

`cases h with c hc`

will turn it into
```
c : mynat,
hc : c + c = 12
```

Of course if you don't want it to be called `c`, you can do `cases h with n hn`
and if you want `n + n = 12` to be called H12 you can do `cases h with n H12`.

-/

/- Tactic : cases
If you have a hypothesis `h : ∃ n, P(n)`
where `P(n)` is a proposition depending on `n`, then
`cases h with d hd`
will produce a new term `d` and also a proof `hd` of `P(d)`. 

## Example

If the local context contains
```
h : ∃ c : mynat, c + c = 12
```

then 

`cases h with c hc`

will turn it into
```
c : mynat,
hc : c + c = 12
```
-/

/-

I also need to tell you that `rw` works on hypotheses as well as on the goal.
In the level below, we have an inequality in the hypothesis as well as in the goal.
So perhaps a natural way to start this level is 

```
rw le_def at h,
rw le_def,
```

and now you can use `cases` on `h` and `use` for the goal.

Pro tip: `rw le_def at h ⊢` does both rewrites at once.
You can get the goal sign by typing `\|-`.
-/

/- Lemma
For all naturals $a$, $b$, if $a\leq b$ then $a\leq \operatorname{succ}(b)$. 
-/
theorem le_succ {a b : mynat} (h : a ≤ b) : a ≤ (succ b) :=
begin [less_leaky]
  rw le_def at h ⊢,
  cases h with c hc,
  use (succ c),
  rw hc,
  rw add_succ,
  refl,


end

/-
Did you use `succ c` or `c + 1` or `1 + c`? Those numbers are all
equal, right? So it doesn't matter which one you use, right?
-/

end mynat -- hide
