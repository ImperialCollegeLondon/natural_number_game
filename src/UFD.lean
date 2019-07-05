import world2_multiplication_core

namespace mynat

def divides (a b : mynat) := ∃ c, a * c = b

instance : has_dvd mynat := ⟨mynat.divides⟩

def is_prime (n : mynat) : Prop := n ≠ one ∧ ∀ d, d ∣ n → d = one ∨ d = n

def strong_induction (P : mynat → Prop)
  (IH : ∀ n : mynat, (∀ m : mynat, m < n → P m) \ 

end mynat