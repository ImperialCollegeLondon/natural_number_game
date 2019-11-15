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
begin [less_leaky]
  intro h,
  cases h with c hc,
  split,
    use succ c,
    rw hc,
    rw succ_add,
    rw add_succ,
    refl,
  intro h,
  cases h with d hd,
  rw hc at hd,
  rw succ_eq_add_one at hd,
  have h : a + 1 + c + d = a + (c + d + 1),
    ring,
  rw h at hd,
  symmetry at hd,
  have h2 := eq_zero_of_add_right_eq_self _ _ hd,
  rw ←succ_eq_add_one at h2,
  exact succ_ne_zero _ h2,



end

/-
Now for the payoff.
-/
end mynat -- hide
