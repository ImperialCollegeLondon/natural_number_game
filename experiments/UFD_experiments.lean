-- WIP

-- this might be awful to do without int.

import solutions.world3_le
import data.nat.basic
#print prefix nat
namespace mynat

def divides (a b : mynat) := ∃ c, a * c = b

instance : has_dvd mynat := ⟨mynat.divides⟩

def is_prime (n : mynat) : Prop := n ≠ 1 ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

-- this should be in world 3
theorem strong_induction (P : mynat → Prop)
  (IH : ∀ m : mynat, (∀ d : mynat, d < m → P d) → P m) :
  ∀ n, P n :=
begin [less_leaky]
  let Q : mynat → Prop := λ m, ∀ d < m, P d,
  have hQ : ∀ n, Q n,
  { intro n,
    induction n with d hd,
    { intros m hm,
      exfalso,
      exact not_lt_zero hm,
    },
    { 
       sorry
    }
  },
  sorry
end

end mynat