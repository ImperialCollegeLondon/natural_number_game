import mynat.le
import solutions.world2_multiplication
import tactic.interactive

#check tactic.interactive.rintro 
meta def less_leaky.interactive.rintro := tactic.interactive.rintro
namespace mynat

theorem le_refl (a : mynat) : a ≤ a :=
begin
  use 0,
  rw add_zero,  
end

-- ignore this; it's making the "refl" tactic work with goals of the form a ≤ a
attribute [_refl_lemma] le_refl

theorem le_succ {a b : mynat} (h : a ≤ b) : a ≤ (succ b) :=
begin
  cases h with c hc,
  use (succ c),
  rw add_succ,
  rw hc,
end

example : one ≤ one := le_refl one

lemma zero_le (a : mynat) : 0 ≤ a :=
begin
  use a,
  rw' zero_add a,
  refl
end

lemma le_zero {a : mynat} : a ≤ 0 → a = 0 :=
begin
  intro h,
  cases h with c hc,
  rw add_comm at hc,
  cases a with b,
    refl,
  exfalso,
  rw add_succ at hc,
  rw eq_comm at hc,
  exact succ_ne_zero hc,
end

theorem le_trans ⦃a b c : mynat⦄ (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
  -- again no induction
  cases hab with x hx,
  cases hbc with y hy,
  use (x + y),
  rw ←add_assoc,
  rw ←hx,
  assumption,
end

instance : preorder mynat := by structure_helper

theorem lt_iff_le_not_le {a b : mynat} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := iff.rfl

theorem le_antisymm : ∀ {{a b : mynat}}, a ≤ b → b ≤ a → a = b :=
begin
  intros a b hab hba,
  cases hab with c hc,
  cases hba with d hd,
  rw hc at hd,
  rw add_assoc at hd,
  rw eq_comm at hd,
  have H := eq_zero_of_add_right_eq_self hd,
  rw eq_comm at hc,
  convert hc,
  symmetry,
  convert add_zero a,
  exact add_right_eq_zero H,
end

instance : partial_order mynat := by structure_helper

theorem lt_iff_le_and_ne ⦃a b : mynat⦄ : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  split,
  { intro h,
    rw lt_iff_le_not_le at h,
    cases h with hab hba,
    split, exact hab,
    intro h,
    apply hba,
    rw' h,
    apply le_refl,
  },
  { intro h,
    cases h with hab hne,
    rw lt_iff_le_not_le,
    split, assumption,
    intro hba,
    apply hne,
    apply le_antisymm hab hba,
  }
end


lemma succ_le_succ {a b : mynat} (h : a ≤ b) : succ a ≤ succ b :=
begin
  cases h with c hc,
  use c,
  rw succ_add,
  rw hc,
end

theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
begin
  revert a,
  induction' b with c hc,
    intro a, right, apply zero_le,
  intro a,
  induction' a with d hd,
    left, apply zero_le,
  cases hc d with h h,
    left, exact succ_le_succ h,
    right, exact succ_le_succ h,
end

instance : linear_order mynat := by structure_helper


theorem add_le_add_right (a b : mynat) : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
  intros h t,
  induction' t with d hd,
  { 
    rw add_zero, rw add_zero,
    assumption
  },
  {
    rw add_succ,
    rw add_succ,
    exact succ_le_succ hd
  }
end

theorem le_succ_self (a : mynat) : a ≤ succ a :=
begin
  apply le_succ,
  apply le_refl
end

theorem le_of_succ_le_succ {a b : mynat} : succ a ≤ succ b → a ≤ b :=
begin
  intro h,
  cases h with c hc,
  use c,
  rw succ_add at hc,
  exact succ_inj hc,
end

theorem not_succ_le_self {{d : mynat}} (h : succ d ≤ d) : false :=
begin
  cases h with c hc,
  rw ←add_one_eq_succ at hc,
  rw add_assoc at hc,
  rw eq_comm at hc,
  have h := eq_zero_of_add_right_eq_self hc,
  rw add_comm at h,
  rw add_one_eq_succ at h,
  apply zero_ne_succ c,
  symmetry,
  assumption,
end

theorem add_le_add_left :
  ∀ (a b : mynat), a ≤ b → ∀ (c : mynat), c + a ≤ c + b :=
begin
  intros a b hab c,
  rw add_comm,
  rw add_comm c,
  apply add_le_add_right,
  assumption
end

def succ_le_succ_iff (a b : mynat) : succ a ≤ succ b ↔ a ≤ b :=
begin
  split,
  { intro h,
    cases h with c hc,
    use c,
    apply succ_inj,
    convert hc,
    rw' succ_add,
    refl
  },
  { intro h,
    cases h with c hc,
    use c,
    rw succ_add,
    rw' hc,
    refl,
  }
end

def succ_lt_succ_iff (a b : mynat) : succ a < succ b ↔ a < b :=
begin
  rw lt_iff_le_not_le,
  rw lt_iff_le_not_le,
  split,
    intro h,
    cases h,
    split,
      rwa succ_le_succ_iff at h_left,
    intro h, apply h_right,
    rwa succ_le_succ_iff,
  intro h,
  cases h,
  split,
    rwa succ_le_succ_iff,
  intro h, apply h_right,
  rwa succ_le_succ_iff at h,  
end

theorem lt_of_add_lt_add_left : ∀ {{a b c : mynat}}, a + b < a + c → b < c :=
begin
  intros a b c,
  intro h,
  rw add_comm at h,
  rw add_comm a at h,
  revert b c,
  induction a with d hd,
    intros a b h, exact h,
  intros b c h,
  rw [add_succ, add_succ] at h,
  apply hd,
  rwa succ_lt_succ_iff at h,
end

theorem le_iff_exists_add : ∀ (a b : mynat), a ≤ b ↔ ∃ (c : mynat), b = a + c :=
begin
  intros a b,
  refl,
end

theorem zero_ne_one : (0 : mynat) ≠ 1 :=
begin
  symmetry,
  rw one_eq_succ_zero,
  apply succ_ne_zero,
end

instance : ordered_comm_monoid mynat := by structure_helper

theorem le_of_add_le_add_left ⦃ a b c : mynat⦄ : a + b ≤ a + c → b ≤ c :=
begin
  intro h,
  cases h with d hd,
  use d,
  rw add_assoc at hd,
  exact add_left_cancel hd
end

instance : ordered_cancel_comm_monoid mynat := by structure_helper

theorem mul_le_mul_of_nonneg_left ⦃a b c : mynat⦄ : a ≤ b → 0 ≤ c → c * a ≤ c * b :=
begin
  intro hab,
  intro hc,
  cases hab with d hd,
  rw hd,
  use c * d,
  rw' mul_add,
  refl
end

theorem mul_le_mul_of_nonneg_right ⦃a b c : mynat⦄ : a ≤ b → 0 ≤ c → a * c ≤ b * c :=
begin
  rw mul_comm,
  rw mul_comm b,
  apply mul_le_mul_of_nonneg_left
end

theorem ne_zero_of_pos ⦃a : mynat⦄ : 0 < a → a ≠ 0 :=
begin
  intro ha,
  intro h,
  rw h at ha,
  rw lt_iff_le_and_ne at ha,
  cases ha with h1 h2,
  apply h2,
  refl,
end

theorem mul_lt_mul_of_pos_left ⦃a b c : mynat⦄ : a < b → 0 < c → c * a < c * b :=
begin
  intros hab hc,
  cases' hab with hab hba,
  rw lt_iff_le_and_ne,
  split,
  { cases hab with d hd,
    use c * d,
    rw hd,
    rw' mul_add,
    refl,
  },
  { intro h,
    apply hba,
    have h2 := mul_left_cancel (ne_zero_of_pos hc) h,
    rw' h2,
    refl
  }

end

theorem mul_lt_mul_of_pos_right ⦃a b c : mynat⦄ : a < b → 0 < c → a * c < b * c :=
begin
  rw mul_comm,
  rw mul_comm b,
  apply mul_lt_mul_of_pos_left,
end

instance : ordered_semiring mynat := by structure_helper

theorem not_lt_zero ⦃a : mynat⦄ : ¬(a < 0) :=
begin [less_leaky]
--  rintro ⟨ha, hna⟩, -- *TODO* -- rintro doesn't work??
  intro h,
  cases h with ha hna,
  apply hna, clear hna,
  --apply le_zero at ha,
  replace ha := le_zero ha,
  rw ha,
  refl,
end

#check @nat.lt_succ_iff
#check @nat.succ_eq_add_one
/-
nat.lt_succ_iff : ∀ {m n : ℕ}, m < nat.succ n ↔ m ≤ n
-/
theorem lt_succ_iff (m n : mynat) : m < succ n ↔ m ≤ n :=
begin [less_leaky]
  rw lt_iff_le_and_ne,
  split,
  { rintro ⟨h1, h2⟩,
    cases h1 with c hc,
    cases c with d,
      exfalso,
      apply h2,
      rw hc,
      rw add_zero,refl,
    use d,
    apply succ_inj,
    rw hc,
    apply add_succ,
  },
  { rintro ⟨c, hc⟩,
    split,
    { use succ c,
      rw hc,
      rw add_succ,
      refl
    },
    { rw hc,
      apply ne_of_lt,
      rw lt_iff_le_and_ne,
      split,
        use succ c,
        rw add_succ,
        refl,
      intro h,
      rw succ_eq_add_one
      rw ←add_zero m at h,
    }
  }
end
end mynat

/-
instance : canonically_ordered_comm_semiring mynat :=
{ add := (+),
  add_assoc := add_assoc,
  zero := 0,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  le := (≤),
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,
  add_le_add_left := add_le_add_left,
  lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  bot := 0,
  bot_le := zero_le,
  le_iff_exists_add := le_iff_exists_add,
  mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  left_distrib := left_distrib,
  right_distrib := right_distrib,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  mul_comm := mul_comm,
  zero_ne_one := zero_ne_one,
  mul_eq_zero_iff := mul_eq_zero_iff }
-/
