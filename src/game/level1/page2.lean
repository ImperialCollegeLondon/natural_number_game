import mynat.definition -- Imports the natural numbers. -- hide

namespace mynat -- hide

/-

## Tutorial world, level 2: `exact`

Your goal is displayed to the right of the `⊢` symbol
in the box on the right. Above this line are your
variables and hypotheses. Click "Click here to prove !"
below to see an example of a theorem with a hypothesis.
-/
/- Lemma
For all natual numbers $a$ and $b$,
if $a=b$, then $a=b$.
-/
lemma example2 (a b : mynat) (h : a = b): a = b :=
begin [less_leaky]
  exact h
end
/-
Our goal is `a = b`, but above the `⊢` symbol you
can see that we have a *hypothesis* `h`, which
is *exactly equal* to the goal. When we are in this
situation, we can close our goal and hence prove our
theorem with the `exact` tactic. Delete `sorry` and
replace it with `exact h,` (**don't forget the comma**),
and you should see the "no goals" message (click just
after the comma if you can't see it). 

These two tactics, `refl` and `exact`, clearly only
have limited capabilities by themselves. The next
tactic we will learn, the rewrite tactic `rw`, is far more powerful.
-/
end mynat -- hide 