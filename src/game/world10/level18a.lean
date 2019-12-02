import game.world10.level17 -- hide
namespace mynat -- hide

-- todo INTRODUCE CONGR

lemma lt_irrefl (a : mynat) : ¬ (a < a) :=
begin [nat_num_game]
  intro h,
  cases h with h1 h2,
  apply h2,
  exact h1,
end

lemma ne_of_lt (a b : mynat) : a < b → a ≠ b :=
begin [nat_num_game]
  intro h,
  intro h1,
  cases h with h2 h3,
  apply h3,
  rw h1,
  refl,
end

-- I had 
-- theorem ne_zero_of_pos (a : mynat) : 0 < a → a ≠ 0 :=
-- do we really need this??

theorem not_lt_zero (a : mynat) : ¬(a < 0) :=
begin [nat_num_game]
  intro h,
  cases h with ha hna,
  apply hna,
  exact zero_le a,
end

theorem lt_of_lt_of_le (a b c : mynat) : a < b → b ≤ c → a < c :=
begin
  intro hab,
  intro hbc,
  rw lt_iff_succ_le at hab ⊢,
  cases hbc with x hx,
  cases hab with y hy,
  rw hx,
  rw hy,
  use y + x,
  ring,
end

theorem lt_of_le_of_lt (a b c : mynat) : a ≤ b → b < c → a < c :=
begin [nat_num_game]
  intro hab,
  intro hbc,
  rw lt_iff_succ_le at hbc ⊢,
  cases hbc with x hx,
  cases hab with y hy,
  rw hx,
  rw hy,
  use y + x,
  rw succ_add,
  rw succ_add,
  rw add_assoc,
  refl,
end

theorem lt_trans (a b c : mynat) : a < b → b < c → a < c :=
begin [nat_num_game]
  intro hab,
  intro hbc,
  rw lt_iff_succ_le at hab hbc ⊢,
  cases hbc with x hx,
  cases hab with y hy,
  rw hx,
  rw hy,
  use y + x + 1,
  repeat {rw succ_add},
  repeat {rw succ_eq_add_one},
  simp,


end



theorem lt_iff_le_and_ne (a b : mynat) : a < b ↔ a ≤ b ∧ a ≠ b :=
begin [nat_num_game]
  split,
    intro h,
    cases h with h1 h2,
    split,
      assumption,
    intro h,
    apply h2,
    rw h,
    refl,
  intro h,
  cases h with h1 h2,
  split,
    exact h1,
  intro h,
  apply h2,
  exact le_antisymm _ _ h1 h


end

theorem lt_succ_self (n : mynat) : n < succ n :=
begin [nat_num_game]
  rw lt_iff_le_and_ne,
  split,
    use 1,
    apply succ_eq_add_one,
  intro h,
  exact ne_succ_self n h
end

lemma succ_le_succ_iff (m n : mynat) : succ m ≤ succ n ↔ m ≤ n :=
begin [nat_num_game]
  split,
    intro h,
    cases h with c hc,
    use c,
    apply succ_inj,
    rw hc,
    rw succ_add,
    refl,
  intro h,
  cases h with c hc,
  use c,
  rw hc,
  rw succ_add,
  refl,



end

-- remind user about succ_le_succ_iff
lemma lt_succ_iff_le (m n : mynat) : m < succ n ↔ m ≤ n :=
begin [nat_num_game]
  rw lt_iff_succ_le,
  exact succ_le_succ_iff m n
end


-- note: needs add_left_cancel but otherwise is easy. 
lemma le_of_add_le_add_left (a b c : mynat) : a + b ≤ a + c → b ≤ c :=
begin [nat_num_game]
  intro h,
  cases h with d hd,
  use d,
  apply add_left_cancel a,
  rw hd,
  ring,



end


lemma lt_of_add_lt_add_left (a b c : mynat) : a + b < a + c → b < c :=
begin [nat_num_game]
  rw lt_iff_succ_le,
  rw lt_iff_succ_le,
  intro h,
  apply le_of_add_le_add_left a,
  rw add_succ,
  exact h,



end

-- I SHOULD TEACH CONGR
lemma add_lt_add_right (a b : mynat) : a < b → ∀ c : mynat, a + c < b + c :=
begin [nat_num_game]
  intro h,
  intro c,
  rw lt_iff_succ_le at h ⊢,
  cases h with d hd,
  use d,
  rw hd,
  repeat {rw succ_add},
  rw add_right_comm,
  refl,


end 

def bot := 0 -- hide
def bot_le := zero_le -- hide
instance : canonically_ordered_monoid mynat := by structure_helper
instance : ordered_comm_monoid mynat := by structure_helper
instance : ordered_cancel_comm_monoid mynat := by structure_helper

def succ_lt_succ_iff (a b : mynat) : succ a < succ b ↔ a < b :=
begin [nat_num_game]
  rw lt_iff_succ_le,
  rw lt_iff_succ_le,
  exact succ_le_succ_iff _ _,



end

-- multiplication

theorem mul_le_mul_of_nonneg_left (a b c : mynat) : a ≤ b → 0 ≤ c → c * a ≤ c * b :=
begin [nat_num_game]
  intro hab,
  intro h0,
  cases hab with d hd,
  rw hd,
  rw mul_add,
  use c * d,
  refl
end

theorem mul_le_mul_of_nonneg_right (a b c : mynat) : a ≤ b → 0 ≤ c → a * c ≤ b * c :=
begin [nat_num_game]
  intro hab,
  intro h0,
  rw mul_comm,
  rw mul_comm b,
  apply mul_le_mul_of_nonneg_left,
    assumption,
  assumption
end


theorem mul_lt_mul_of_pos_left (a b c : mynat) : a < b → 0 < c → c * a < c * b :=
begin [nat_num_game]
  intro hab,
  intro hc,
  cases c with d,
    exfalso,
    exact lt_irrefl 0 hc,
  clear hc,
  induction d with e he,
    rw [succ_mul,zero_mul, zero_add, succ_mul, zero_mul, zero_add],
    exact hab,
  rw succ_mul,
  rw succ_mul (succ e),
  have h : succ e * a + a < succ e * b + a,
    exact add_lt_add_right _ _ he _,
  apply lt_trans _ _ _ h,
  rw add_comm,
  rw add_comm _ b,
  apply add_lt_add_right,
  assumption
end

theorem mul_lt_mul_of_pos_right (a b c : mynat) : a < b → 0 < c → a * c < b * c :=
begin [nat_num_game]
  intros ha h0,
  rw mul_comm,
  rw mul_comm b,
  apply mul_lt_mul_of_pos_left,
  assumption,
  assumption
end

instance : ordered_semiring mynat := by structure_helper

lemma le_mul (a b c d : mynat) : a ≤ b → c ≤ d → a * c ≤ b * d :=
begin [nat_num_game]
intros hab hcd,
cases a with t Ht,
  rw [zero_mul],
  apply zero_le,
have cz : 0 ≤ c,
  apply zero_le,
have bz : 0 ≤ b,
  apply zero_le,
apply mul_le_mul hab hcd cz bz,
end

lemma pow_le (m n a : mynat) : m ≤ n → m ^ a ≤ n ^ a :=
begin [nat_num_game]
intro h,
induction a with t Ht,
  rw [pow_zero, pow_zero],
  refl,
rw [pow_succ, pow_succ],
apply le_mul,
  assumption,
assumption,
end

lemma strong_induction_aux (P : mynat → Prop)
  (IH : ∀ m : mynat, (∀ b : mynat, b < m → P b) → P m)
  (n : mynat) : ∀ c < n, P c :=
begin [nat_num_game]
  induction n with d hd,
    intro c,
    intro hc,
    exfalso,
    revert hc,
    exact not_lt_zero c,
  intros e he,
  rw lt_succ_iff_le at he,
  apply IH,
  intros b hb,
  apply hd,
  exact lt_of_lt_of_le _ _ _ hb he
end

-- is elab_as_eliminator right?
@[elab_as_eliminator]
theorem strong_induction (P : mynat → Prop)
  (IH : ∀ m : mynat, (∀ d : mynat, d < m → P d) → P m) :
  ∀ n, P n :=
begin [nat_num_game]
  intro n,
  apply strong_induction_aux P IH (succ n),
  exact lt_succ_self n
end

end mynat -- hide
