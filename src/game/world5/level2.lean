import game.world5.level1 -- hide
namespace mynat -- hide

/-
# World 5 : Inequality world 

## Level 2 : `le_succ`

Perhaps a natural way to start this level is 

```
rw le_def at h,
rw le_def,
```

and now you can use `cases` on `h` and `use` for the goal.

Pro tip: `rw le_def at h ⊢` does both rewrites at once.
You can get the goal sign by typing `\|-`.

Even pro-er tip: the rewrites aren't actually necessary!
They are true by definition, so actually you can just skip them.
It's more readable if you put them in, but quicker if you don't.
-/

/- Lemma
For all naturals `a`, `b`, if `a ≤ b` then `a ≤ succ(b)`. 
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
end mynat -- hide
