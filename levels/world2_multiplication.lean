import solutions.world1_addition -- addition lemmas

import mynat.mul
/- Here's what you get from the import:

1) The following data:
  * a function called mynat.mul, and notation a * b for this function

2) The following axioms:

  * `mul_zero : ∀ a : mynat, a * 0 = 0`
  * `mul_succ : ∀ a b : mynat, a * succ(b) = a * b + a`

These axiom between them tell you how to work out a * x for every x; use induction on x to
reduce to the case either `x = 0` or `x = succ b`, and then use `mul_zero` or `mul_succ` appropriately.
-/

namespace mynat


lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin [less_leaky]
  sorry
end

lemma mul_one (m : mynat) : m * 1 = m :=
begin [less_leaky]
  sorry
end

lemma one_mul (m : mynat) : 1 * m = m :=
begin [less_leaky]
  sorry
end

-- mul_assoc immediately, leads to this:
-- ⊢ a * (b * d) + a * b = a * (b * d + b)

-- so let's prove mul_add first.

lemma mul_add (a b c : mynat) : a * (b + c) = a * b + a * c :=
begin [less_leaky]
  sorry
end

-- just ignore this
def left_distrib := mul_add -- stupid field name, 
-- I just don't instinctively know what left_distrib means

lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin [less_leaky]
  sorry
end

-- goal : mul_comm. 
-- mul_comm leads to ⊢ a * d + a = succ d * a
-- so perhaps we need add_mul
-- but add_mul leads to either a+b+c=a+c+b or (a+b)+(c+d)=(a+c)+(b+d)
-- (depending on whether we do induction on b or c)

-- I need this for mul_comm
lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin [less_leaky]
  sorry
end

lemma add_mul (a b c : mynat) : (a + b) * c = a * c + b * c :=
begin [less_leaky]
  sorry
end

-- ignore this
def right_distrib := add_mul -- stupid field name, 

lemma mul_comm (a b : mynat) : a * b = b * a :=
begin [less_leaky]
  sorry
end

theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin [less_leaky]
  sorry
end

theorem eq_zero_or_eq_zero_of_mul_eq_zero ⦃a b : mynat⦄ (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin [less_leaky]
  sorry
end

theorem mul_eq_zero_iff : ∀ (a b : mynat), a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin [less_leaky]
  sorry
end

instance : comm_semiring mynat := by structure_helper

theorem mul_left_cancel ⦃a b c : mynat⦄ (ha : a ≠ 0) : a * b = a * c → b = c :=
begin [less_leaky]
  sorry
end

end mynat
