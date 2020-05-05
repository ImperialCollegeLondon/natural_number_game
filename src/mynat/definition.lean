import tactic.structure_helper
import tactic.nat_num_game
/-

  mynat/definition.lean -- definition of mynat.
  
  Supplies:
  constants zero : mynat and one : mynat
  function S : mynat → mynat
  notation 0 for zero and 1 for one.

The below code will be *invisible to the player*
-/

-- definition of "the natural numbers"
@[derive decidable_eq]
inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

namespace mynat

instance : has_zero mynat := ⟨mynat.zero⟩
@[leakage] theorem mynat_zero_eq_zero : mynat.zero = 0 := rfl

def one : mynat := succ 0

instance : has_one mynat := ⟨mynat.one⟩

theorem one_eq_succ_zero : 1 = succ 0 := rfl

lemma zero_ne_succ (m : mynat) : (0 : mynat) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : mynat} (h : succ m = succ n) : m = n := by cases h; refl

end mynat

attribute [symm] ne.symm
