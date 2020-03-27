import game.world10.level15 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 16: equivalence of two definitions of `<`

Now let's go the other way. 
-/

/- Lemma : 
For all naturals $a$ and $b$,
$$
\operatorname{succ}(a)\le b
\implies
a\le b\land\lnot(b\le a).$$
-/
lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=
begin [nat_num_game]
  intro h,
  split,
  apply le_trans a (succ a) b,
  exact le_succ_self a,
  exact h,

  intro nh,
  apply ne_succ_self a,
  apply le_antisymm a (succ a),
  exact le_succ_self a,
  exact le_trans (succ a) b a h nh,

end

/-
Now for the payoff.
-/
end mynat -- hide
