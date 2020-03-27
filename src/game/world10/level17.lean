import game.world10.level16 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 17: definition of `<`

OK so we are going to *define* `a < b` by `a ≤ b ∧ ¬ (b ≤ a)`,
and given `lt_aux_one a b` and `lt_aux_two a b` it should now just
be a few lines to prove `a < b ↔ succ(a) ≤ b`. 

-/

definition lt (a b : mynat) := a ≤ b ∧ ¬ (b ≤ a)

-- incantation so that we can use `<` notation: 
instance : has_lt mynat := ⟨lt⟩

/- Lemma : 
For all naturals $a$ and $b$,
$$a<b\iff\operatorname{succ}(a)\le b.$$
-/
lemma lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b :=
begin [nat_num_game]
  split,
    exact lt_aux_one a b,
  exact lt_aux_two a b,


end

end mynat -- hide
