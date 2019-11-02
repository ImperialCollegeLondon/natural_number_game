import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level6andahalf -- hide
namespace mynat -- hide

/- Tactic : have
The `have` tactic is a way to prove an intermediate lemma,
in the middle of your proof.



If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
and your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s. If you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l`).

### Example:

If your local context (the top right window) looks like this
```
a b : mynat,
h : succ (succ a) = succ (succ b)
⊢ a = b
```

then after `have h2 : succ(a)=succ(b)` it will look like this:

```
2 goals
a b : mynat,
h : succ (succ a) = succ (succ b)
⊢ succ a = succ b

a b : mynat,
h : succ (succ a) = succ (succ b),
h2 : succ a = succ b
⊢ a = b
```

Note that we have to prove a new goal now, but note also that the second
goal now has `h2 : succ a = succ b` as an extra hypothesis which wasn't
there before.
-/

/-

# World 2 -- Addition World

## Level 6 and three quarters:  -- `succ_succ_inj`.
-/

/-
In the below theorem, we need to apply `succ_inj` twice. Once to prove
$succ(succ(a))=succ(succ(b))\implies succ(a)=succ(b)$, and then again
to prove $succ(a)=succ(b)\implies a=b$. However `succ(a)=succ(b)` is
nowhere to be found, it's neither an assumption or a goal when we start
this levl. If we're going to follow our proof sketch above
then we are going to have to prove it along the way, and the `have` tactic
lets us do this.

Delete the `sorry` below and try this for the first line of your proof:

`have h2 : succ(a)=succ(b),`

and look what happens: a new goal appears! We've seen the `induction` tactic
change one goal into two, but the `have` tactic does it in a far more
simplistic way -- it just creates an extra goal with the idea that if we can
solve this new goal then the corresponding proof will help us along the way to solving
our original goal.

You can close this new goal with ease. We want to apply `succ_inj` to
hypothesis h, so

`exact succ_inj(h),`

will do it.

After you remember the command and hit enter, you're back down to one goal, but
now we have a proof of `h2 : succ(a)=succ(b)`. So we can deduce `a = b` with
another application of `succ_inj`: 

`exact succ_inj(h2),`

and you're home. 
-/
/- Theorem
For all naturals $a$ and $b$, if we assume $succ(succ(a))=succ(succ(b))$, then we can
deduce $a=b$. 
-/
theorem succ_succ_inj {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin [less_leaky]
    have h2 : succ(a)=succ(b),
      exact succ_inj(h),
    exact succ_inj(h2),



end

end mynat -- hide