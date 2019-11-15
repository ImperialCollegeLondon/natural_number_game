--import mynat.lt -- definition of <
import game.world10.level14 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 15: introducing `<`

To get the remaining collectibles in this world, we need to
give a definition of `<`. By default, the definition of `a < b`
in Lean, once `≤` is defined, is this:

`a < b := a ≤ b ∧ ¬ (b ≤ a)`

. But a much more usable definition would be this:

`a < b := succ(a) ≤ b`

. Let's prove that these two definitions are the same
-/

/- Lemma : 
For all naturals $a$ and $b$,
$$a\le b\land\lnot(b\le a)\implies\operatorname{succ}(a)\le b.$$
-/
lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=
begin [less_leaky]
  intro h,
  cases h with h1 h2,
  cases h1 with c hc,
  cases c with d,
    exfalso,
    rw add_zero at hc,
    apply h2,
    rw hc,
    refl,
  use d,
  rw hc,
  rw add_succ,
  rw succ_add,
  refl,


end


def lt_of_add_lt_add_left : ∀ (a b c : mynat), a + b < a + c → b < c := sorry

def bot := 0
def bot_le := zero_le
instance : canonically_ordered_monoid mynat := by structure_helper
instance : ordered_comm_monoid mynat := by structure_helper

end mynat -- hide
