import mynat.definition -- Imports the natural numbers. -- hide

namespace mynat -- hide

/-

## Tutorial world, level 2: the `exact` tactic.

Your goal is displayed to the right of the `⊢` symbol
in the box on the right. Above this line are your
variables and hypotheses. Click "Click here to prove !"
below to see an example of a theorem with a hypothesis.

Here you can see that you have a *hypothesis* `h`,
which is *exactly* equal to your goal. In
this situation, the tactic

`exact h,`

should do it. Don't forget the `h`, and don't forget
the comma! Try it below. Delete the sorry and replace
it with `exact h,`. Hit enter after the comma
to go onto a new line. Don't forget the `h` and
don't forget the comma.
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
You should see the "no goals" message. The reason
this works is that the goal is *exactly h*.

These two tactics, `refl` and `exact`, clearly only
have limited capabilities by themselves. The next
tactic we will learn, the rewrite tactic `rw`, is far more powerful.
-/
end mynat -- hide 