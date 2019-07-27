-- WIP

-- this might be awful to do without int.

import solutions.world3_le
import data.nat.basic
#print prefix nat
namespace mynat

def divides (a b : mynat) := ∃ c, a * c = b

instance : has_dvd mynat := ⟨mynat.divides⟩

def is_prime (n : mynat) : Prop := n ≠ 1 ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

theorem has_prime_factor (n : mynat) : 1 < n → ∃ p : mynat, is_prime p ∧ p ∣ n :=
begin [less_leaky]
  intro h,
  cases n with n,
    exfalso, apply @not_lt_zero 1,
    exact h,
  cases n with n,
    exfalso,
    rw ←one_eq_succ_zero at h,
    apply lt_irrefl (1 : mynat),
    assumption,
  clear h,
  revert n,
  apply strong_induction,
  -- strong induction successfully applied!
  sorry
end

end mynat