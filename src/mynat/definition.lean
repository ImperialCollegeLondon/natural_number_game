/-

  mynat/definition.lean -- definition of mynat.
  
  Supplies:
  constants zero : mynat and one : mynat
  function S : mynat → mynat
  notation 0 for zero and 1 for one.
-/

-- The below code will be *invisible to the player*

import structure_helper

-- definition of "the natural numbers"
inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

namespace mynat

instance : has_zero mynat := ⟨mynat.zero⟩

def one : mynat := succ 0

instance : has_one mynat := ⟨mynat.one⟩

lemma zero_ne_succ (m : mynat) : (0 : mynat) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : mynat} (h : succ m = succ n) : m = n := by cases h; refl

-- end of definition of naturals

end mynat
