import game.world6.level8 -- hide
import tactic.tauto
local attribute [instance, priority 10] classical.prop_decidable -- hide
/- 
# Advanced proposition world. 

## Level 10: `exfalso` and proof by contradiction. 

It's certainly true that $(P\land(\lnot P)\implies Q$ for any propositions $P$
and $Q$, because the left hand side of the implication is false. But how do
we prove that `false` implies any proposition $Q$? A cheap way of doing it in
Lean is using the `exfalso` tactic, which changes any goal at all to `false`. 
You might think this is a step backwards, but if you have a hypothesis `h : ¬ P`
then after `rw not_iff_imp_false at h,` you can `apply h,` to make progress. 
Try solving this level without using `cc` or `tauto`, but using `exfalso` instead.

-/



/- Lemma
If $P$ and $Q$ are true/false statements, then
$$(P\land(\lnot P))\implies Q.$$
-/
lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
begin
  intro h,
  cases h with p np,
  rw not_iff_imp_false at np,
  exfalso,
  apply np,
  exact p,


end

/-
OK that's enough logic -- now perhaps it's time to go on to Advanced Addition World!
Get to it via the main menu.
-/

/-
## Pro tip.

`¬ P` is actually `P → false` *by definition*. Try
commenting out `rw not_iff_imp_false at ...` by putting two minus signs `--`
before the `rw`. Does it still compile?
-/