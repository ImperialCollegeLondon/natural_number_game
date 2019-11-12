import game.world10.level14 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 10: `le_succ_self`

Can you find the two-line proof?
-/

/- Lemma
For all naturals $a$, $a\le\operatorname{succ}(a).$
-/
lemma add_le_add_left' (a : mynat) : a ≤ succ a :=
begin [less_leaky]
  use 1,
  refl,
  

end


--def lt_of_add_lt_add_left : ∀ (a b c : mynat), a + b < a + c → b < c := sorry

def bot := 0
def bot_le := zero_le
def le_iff_exists_add : ∀ (a b : mynat), a ≤ b ↔ ∃ (c : mynat), b = a + c :=
by intros; exact iff.rfl
instance : canonically_ordered_monoid mynat := by structure_helper

instance : ordered_comm_monoid mynat := by structure_helper

end mynat -- hide
