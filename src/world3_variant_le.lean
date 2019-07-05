import world2_multiplication_core

-- ***first goal should be ordered_comm_monoid***

import tactic.linarith

-- this is one of *three* routes to
-- canonically_ordered_comm_semiring

namespace mynat

def le (a b : mynat) := ∃ c :  mynat, a + c = b

-- Third choices: 
-- | le 0 _
-- | le (succ a) (succ b) = le ab 

-- notation
instance : has_le mynat := ⟨mynat.le⟩

-- this attribute must go
@[_refl_lemma]
theorem le_refl (a : mynat) : a ≤ a :=
begin
  use 0,
  rw add_zero,  
end

theorem le_succ {a b : mynat} (h : a ≤ b) : a ≤ (succ b) :=
begin
  cases h with c hc,
  use (succ c),
  rw add_succ,
  rw hc,
end

example : one ≤ one := le_refl one

lemma zero_le (a : mynat) : zero ≤ a :=
begin
  use a, exact zero_add a,
--  induction a also works
end

lemma le_zero {a : mynat} : a ≤ zero → a = zero :=
begin
  intro h,
  cases h with c hc,
  rw add_comm at hc,
  cases a with b,
    refl,
  exfalso,
  rw add_succ at hc,
  rw eq_comm at hc,
  exact zero_ne_succ _ hc,
end

lemma succ_le_succ {a b : mynat} (h : a ≤ b) : succ a ≤ succ b :=
begin
  -- no induction needed
  cases h with c hc,
  use c,
  rw succ_add,
  rw hc,
end

-- one of the axioms for ordered semiring or whatever
theorem add_le_add_right (a b : mynat) : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
  intros h t,
  induction t with d hd,
  { 
    exact h
  },
  {
    rw add_succ,
    rw add_succ,
    exact succ_le_succ hd
  }
end

-- it's better with implicits surely?
theorem le_trans' {a b c : mynat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
  -- again no induction
  cases hab with x hx,
  cases hbc with y hy,
  use (x + y),
  rw ←add_assoc,
  rw hx,
  assumption,
end

theorem le_trans (a b c : mynat) : a ≤ b → b ≤ c → a ≤ c := le_trans'

theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
begin
  revert a,
  induction b with c hc,
    intro a, right, apply zero_le,
  intro a,
  induction a with d hd,
    left, apply zero_le,
  cases hc d with h h,
    left, exact succ_le_succ h,
    right, exact succ_le_succ h,
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

theorem le_antisymm : ∀ {a b : mynat}, a ≤ b → b ≤ a → a = b :=
begin
  intros a b hab hba,
  cases hab with c hc,
  cases hba with d hd,
  rw ←hc at hd,
  rw add_assoc at hd,
  have H := eq_zero_of_add_right_eq_self hd,
  apply add_right_eq_self
  revert a, -- switcheroo
  induction b with d hd,
  {
    intros a ha h,
    exact le_zero ha
  },
  { intro a,
    cases a with a,
      intros h1 h2, cases h2,
    intros had hda,
    congr,
    apply hd,
      cases had,
      apply le_of_succ_le_succ,
        assumption,
        refine le_trans' _ had_a_1,
          apply le_succ,
        apply le_refl,
      cases hda,
        apply le_refl,
      apply le_trans' _ hda_a_1,
    apply le_succ_self,
  }
end

theorem not_succ_le_self {d : mynat} (h : succ d ≤ d) : false :=
begin
--  induction h, -- wtf?
  revert h,
  induction d with a ha,
    intro h,
    cases h,
  intro h,
  apply ha,
  apply le_of_succ_le_succ,
  assumption,
end

theorem not_succ_le_self' (d : mynat) (h : succ d ≤ d) : false := not_succ_le_self h

theorem le_antisymm' {b : mynat} : ∀ {a : mynat}, b ≤ a → a ≤ b → a = b :=
begin
  induction b with d hd,
  {
    intros a ha h,
    cases ha,
    refl,
    apply le_zero,
    assumption,
  },
  { intro a,
    induction a with b hb,
    { intros h1 h_irrelevant,
      symmetry,
      apply le_zero,
      assumption,
    },
    { intros h1 h2,
      cases h2 with _ _ _ sald, -- leakage and _
        refl,
      exfalso,
      apply not_succ_le_self' d,
      apply le_trans' h1 sald },
  }
end

--def lt : mynat → mynat → Prop := λ a b, a ≤ b ∧ ¬ b ≤ a

--instance : has_lt mynat := ⟨mynat.lt⟩

def bot : mynat := 0

instance : lattice.has_bot mynat := ⟨mynat.bot⟩

def bot_le : ∀ a : mynat, ⊥ ≤ a := zero_le

theorem succ_ne_zero : ∀ {a : mynat}, succ a ≠ 0 := 
begin
  intro a, intro ha, cases ha,
end

theorem mul_eq_zero_iff : ∀ (a b : mynat), a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin
  intros a b,
  split, swap,
    intro hab, cases hab,
      rw hab, rw zero_mul,
    rw hab, rw mul_zero,
  intro hab,
  cases a with d,
    change 0 * b = 0 at hab, -- leak
    left, refl,
  cases b with e he,
    right, refl,
  exfalso,
  change succ _ = 0 at hab,
  -- succ (add (mul (succ d) e) d) = 0 -- aargh
  exact succ_ne_zero hab,
end

-- #check lt_iff_le_not_le
-- : ?M_3 < ?M_4 ↔ ?M_3 ≤ ?M_4 ∧ ¬?M_4 ≤ ?M_3
--def lt_iff_le_not_le {a b c : mynat} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := iff.rfl

-- #check mynat.zero

instance : preorder mynat :=
{ le := mynat.le,
  le_refl := mynat.le_refl,
  le_trans := mynat.le_trans,
  }

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
    intro h,
    cases h,
      refl,
    refine le_trans' _ h_a_1,
    exact le_succ_self _,
  exact succ_le_succ,
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

theorem lt_if_add_lt_add_left : ∀ (a b c : mynat), a + b < a + c → b < c :=
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
  split,
    intro h,
    induction b with d hd,
      use 0,
      rw add_zero,
      symmetry,
      apply le_zero,
      assumption,
    cases h,
      use 0,
      rw add_zero,
    cases hd h_a_1 with c hc,
    use (succ c),
    rw hc,
    rw add_succ,
  intro h,
  rcases h with ⟨c, rfl⟩,
  induction c with d hd,
    refl,
  apply le_trans' hd,
  rw add_succ,
  exact le_succ_self _, 
end


theorem zero_ne_one : (0 : mynat) ≠ 1 :=
begin
  intro h, rw eq_comm at h, revert h,
  exact succ_ne_zero,
end

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
  le_antisymm := λ a b, le_antisymm,
  add_le_add_left := add_le_add_left,
  lt_of_add_lt_add_left := lt_if_add_lt_add_left,
  bot := ⊥,
  bot_le := bot_le,
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

end mynat
