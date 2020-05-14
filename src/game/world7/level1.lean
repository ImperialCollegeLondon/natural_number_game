/- 

# Advanced proposition world. 

In this world we will learn five key tactics needed to solve all the
levels of the Natural Number Game, namely `split`, `cases`, `left`, `right`, and `exfalso`.
These, and `use` (which we'll get to in Inequality World) are all the
tactics you will need to beat all the levels of the game.

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

/- Tactic : split

## Summary:

If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.

## Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

## Example:

If your local context (the top right window) looks like this
```
a b : mynat,
⊢ a = b ↔ a + 3 = b + 3
```

then after

`split,`

it will look like this:

```
2 goals
a b : mynat
⊢ a = b → a + 3 = b + 3

a b : mynat
⊢ a + 3 = b + 3 → a = b

-/
