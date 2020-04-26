import game.world10.level17 -- every level of the natural number game on the web
import game.world3.level7 -- semiring instance
namespace mynat

/-
Here are the remaining lt (less than) levels. 

-/
lemma lt_irrefl (a : mynat) : ¬ (a < a) :=
begin [nat_num_game]
  sorry
end

lemma ne_of_lt {a b : mynat} : a < b → a ≠ b :=
begin [nat_num_game]
  sorry
end

theorem not_lt_zero (a : mynat) : ¬(a < 0) :=
begin [nat_num_game]
  sorry
end

theorem lt_of_lt_of_le {a b c : mynat} : a < b → b ≤ c → a < c :=
begin
  sorry
end

theorem lt_of_le_of_lt {a b c : mynat} : a ≤ b → b < c → a < c :=
begin [nat_num_game]
  sorry
end

theorem lt_trans (a b c : mynat) : a < b → b < c → a < c :=
begin [nat_num_game]
  sorry
end

theorem lt_iff_le_and_ne (a b : mynat) : a < b ↔ a ≤ b ∧ a ≠ b :=
begin [nat_num_game]
  sorry
end

theorem lt_succ_self (n : mynat) : n < succ n :=
begin [nat_num_game]
  sorry
end

-- This one isn't about < but it's convenient for the next level
lemma succ_le_succ_iff (m n : mynat) : succ m ≤ succ n ↔ m ≤ n :=
begin [nat_num_game]
  sorry
end

lemma lt_succ_iff_le (m n : mynat) : m < succ n ↔ m ≤ n :=
begin [nat_num_game]
  sorry
end

-- note: needs add_left_cancel but otherwise is easy. 
lemma le_of_add_le_add_left (a b c : mynat) : a + b ≤ a + c → b ≤ c :=
begin [nat_num_game]
  sorry
end


lemma lt_of_add_lt_add_left (a b c : mynat) : a + b < a + c → b < c :=
begin [nat_num_game]
  sorry
end

lemma add_lt_add_right (a b : mynat) : a < b → ∀ c : mynat, a + c < b + c :=
begin [nat_num_game]
  sorry
end 

-- and now we get three achievements!
instance : ordered_comm_monoid mynat := 
{ add_le_add_left := λ _ _, add_le_add_left,
  lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  ..mynat.add_comm_monoid, ..mynat.partial_order}
instance : canonically_ordered_monoid mynat := 
{ le_iff_exists_add := le_iff_exists_add,
  bot := 0,
  bot_le := zero_le,
  ..mynat.ordered_comm_monoid,
  }
instance : ordered_cancel_comm_monoid mynat := 
{ add_left_cancel := add_left_cancel,
  add_right_cancel := add_right_cancel,
  le_of_add_le_add_left := le_of_add_le_add_left,
  ..mynat.ordered_comm_monoid}

-- But these are all about the relation between < and +; we now need to
-- understand the difference between < and *.

def succ_lt_succ_iff (a b : mynat) : succ a < succ b ↔ a < b :=
begin [nat_num_game]
  sorry
end

-- multiplication

theorem mul_le_mul_of_nonneg_left (a b c : mynat) : a ≤ b → 0 ≤ c → c * a ≤ c * b :=
begin [nat_num_game]
  sorry
end

theorem mul_le_mul_of_nonneg_right (a b c : mynat) : a ≤ b → 0 ≤ c → a * c ≤ b * c :=
begin [nat_num_game]
  sorry
end

-- this is long
theorem mul_lt_mul_of_pos_left (a b c : mynat) : a < b → 0 < c → c * a < c * b :=
begin [nat_num_game]
  sorry
end

theorem mul_lt_mul_of_pos_right (a b c : mynat) : a < b → 0 < c → a * c < b * c :=
begin [nat_num_game]
  sorry
end

-- And now another achievement! The naturals are an ordered semiring.
instance : ordered_semiring mynat := 
{ mul_le_mul_of_nonneg_left := mul_le_mul_of_nonneg_left,
  mul_le_mul_of_nonneg_right := mul_le_mul_of_nonneg_right,
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
  ..mynat.semiring,
  ..mynat.ordered_cancel_comm_monoid
}
-- a couple more bits and bobs just for fun
lemma le_mul (a b c d : mynat) : a ≤ b → c ≤ d → a * c ≤ b * d :=
begin [nat_num_game]
  sorry
end

lemma pow_le (m n a : mynat) : m ≤ n → m ^ a ≤ n ^ a :=
begin [nat_num_game]
  sorry
end

-- Now the boss level: prove strong induction!
-- The trick is to prove this first.
lemma strong_induction_aux (P : mynat → Prop)
  (IH : ∀ m : mynat, (∀ b : mynat, b < m → P b) → P m)
  (n : mynat) : ∀ c < n, P c :=
begin [nat_num_game]
  sorry
end

-- Now strong induction should be easy.
@[elab_as_eliminator]
theorem strong_induction (P : mynat → Prop)
  (IH : ∀ m : mynat, (∀ d : mynat, d < m → P d) → P m) :
  ∀ n, P n :=
begin [nat_num_game]
  sorry
end

end mynat
