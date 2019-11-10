-- World name : Advanced Proposition world
/- 

# Advanced proposition world. 

In this world we will learn the last five tactics needed to solve all the
levels of the Natural Number Game, namely `cases`, `split`, `left`, `right` and `use`.

TODO -- change order to order we learn them in (here and in Prop world level 9)

## Level 1: the `split` tactic.

The logical symbol `∧` means "and". If $P$ and $Q$ are propositions, then
$P\land Q$ is the proposition "$P$ and $Q$". If your *goal* is `P ∧ Q` then
you can make progress with the `split` tactic, which turns one goal `⊢ P ∧ Q`
into two goals, namely `⊢ P` and `⊢ Q`. In the level below, after a `split`,
you will be able to finish off the goals with the `exact` tactic.
-/

/- Lemma : no-side-bar
If $P$ and $Q$ are true, then $P\land Q$ is true.
-/
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=
begin
  split,
  exact p,
  exact q,


end 

