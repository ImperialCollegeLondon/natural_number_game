import world3_le_solutions

namespace mynat

def divides (a b : mynat) := ∃ c, a * c = b

instance : has_dvd mynat := ⟨mynat.divides⟩

def is_prime (n : mynat) : Prop := n ≠ 1 ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

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