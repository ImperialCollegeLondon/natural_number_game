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
/-
For now -- that's it. In the next version of the natural number game we will go on and make
the natural numbers into an `ordered_cancel_comm_monoid`, which is the most
exotic of all the structures defined on the natural numbers in Lean 3.4.2.

Interested in playing levels involving other kinds of mathematics?
Look <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/WHATS_NEXT.md"
  target="blank">here</a> for more ideas about what to do next.

Interested in learning more? Join us on the
<a href="https://leanprover.zulipchat.com/" target="blank">Zulip Lean chat</a>
and ask questions in the `#new members` stream. Real names preferred. Be nice.
-/

end mynat -- hide
