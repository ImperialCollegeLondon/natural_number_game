import game.world7.level5 -- hide
/- 
# Advanced proposition world. 

## Level 6: Or, and the `left` and `right` tactics.

`P ∨ Q` means "$P$ or $Q$". So to prove it, you
need to choose one of `P` or `Q`, and prove that one.
If `⊢ P ∨ Q` is your goal, then `left` changes this
goal to `⊢ P`, and `right` changes it to `⊢ Q`.
Note that you can take a wrong turn here. Let's
start with trying to prove $Q\implies (P\lor Q)$.
After the `intro`, one of `left` and `right` leads
to an impossible goal, the other to an easy finish.
-/



/- Lemma : no-side-bar
If $P$ and $Q$ are true/false statements, then
$$Q\implies(P\lor Q).$$ 
-/
example (P Q : Prop) : Q → (P ∨ Q) :=
begin
  intro q,
  right,
  assumption,


end
/- Tactic : left and right

## Summary

`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.

## Details

The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`. 
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.
-/
