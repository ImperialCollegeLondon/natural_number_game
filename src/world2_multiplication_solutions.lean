import world1_addition_solutions
import mynat.mul

namespace mynat

lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin
  induction m with d hd,
  {
    refl
  },
  {
    rw mul_succ,
    rw hd,
    refl
  }
end

lemma mul_one (m : mynat) : m * 1 = m :=
begin
  show m * (succ 0) = m,
  rw mul_succ,
  rw mul_zero,
  exact zero_add m,
end

lemma one_mul (m : mynat) : 1 * m = m :=
begin
  induction m with d hd,
  {
    refl,
  },
  {
    rw mul_succ,
    rw hd,
    exact add_one_eq_succ d,
  }
end

-- mul_assoc immediately, leads to this:
-- ⊢ a * (b * d) + a * b = a * (b * d + b)

lemma mul_add (a b c : mynat) : a * (b + c) = a * b + a * c :=
begin
  induction c with d hd,
  {
    refl
  },
  {
    rw add_succ,
-- or    show a * succ (b + d) = _,
    rw mul_succ,
-- or    show a * (b + d) + _ = _,
    rw hd,
    rw mul_succ,
    apply add_assoc, -- ;-)
  }
end

-- hide this
def left_distrib := mul_add -- stupid field name, 
-- I just don't instinctively know what left_distrib means

lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin
  induction c with d hd,
  { 
    refl
  },
  {
    rw mul_succ,
    rw mul_succ,
--    show (a * b) * d + (a * b) = _,
    rw hd,
--    show _ = a * (b * d + _),
    rw mul_add
  }
end

-- goal : mul_comm. 
-- mul_comm leads to ⊢ a * d + a = succ d * a
-- so perhaps we need add_mul
-- but add_mul leads to either a+b+c=a+c+b or (a+b)+(c+d)=(a+c)+(b+d)
-- (depending on whether we do induction on b or c)

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
  rw add_assoc,
  rw add_comm b c,
  rw ←add_assoc,
end

-- I need this for mul_comm
lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin
  induction b with d hd,
  {
    refl
  },
  {
    rw mul_succ,
    rw mul_succ,
--    show (succ a) * d + (succ a) = (a * d + a) + _,
    rw hd,
    rw add_succ,
    rw add_succ,
    rw add_right_comm
  }
end

-- turns out I don't actually need this for mul_comm
lemma add_mul (a b c : mynat) : (a + b) * c = a * c + b * c :=
begin
  induction' b with d hd,
  { 
    rw zero_mul,
    rw add_zero,
    rw' add_zero,
    refl
  },
  {
    rw add_succ,
    rw succ_mul,
    rw hd,
    rw succ_mul,
    rw' add_assoc,
    refl
  }
end

def right_distrib := add_mul -- stupid field name, 

lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
  induction' b with d hd,
  { 
    rw zero_mul,
    rw mul_zero,
  },
  {
    rw succ_mul,
    rw ←hd,
    rw mul_succ,
  }
end

-- this is < axiom 4
theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
  intros ha hb,
  intro hab,
  cases b with b,
    apply hb,
    refl,
  rw mul_succ at hab,
  apply ha,
  cases a with a,
    refl,
  rw add_succ at hab,
  exfalso,
  apply succ_ne_zero hab
end

-- this involves a lot of cases. Would be really cool
-- to have some sort of trickery instead of all the {}s.
theorem mul_eq_zero_iff : ∀ (a b : mynat), a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin
  intros a b,
  split, swap,
    intro hab, cases hab,
      rw hab, rw zero_mul,
    rw hab, rw mul_zero,
  intro hab,
  cases' a with d,
    left, refl,
  cases b with e he,
    right, refl,
  exfalso,
  rw mul_succ at hab,
  rw add_succ at hab,
  exact succ_ne_zero hab,
end

theorem eq_zero_or_eq_zero_of_mul_eq_zero ⦃a b : mynat⦄ (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  revert a,
  induction' b with c hc,
  { intros a ha,
    right, refl,
  },
  { intros a ha,
    rw mul_succ at ha,
    left,
    apply add_left_eq_zero ha
  }
end

instance : comm_semiring mynat := by structure_helper

theorem mul_left_cancel ⦃a b c : mynat⦄ (ha : a ≠ 0) : a * b = a * c → b = c :=
begin
  revert b,
  induction' c with d hd,
  { intro b,
    rw mul_zero,
    intro h,
    cases (eq_zero_or_eq_zero_of_mul_eq_zero h),
      exfalso,
      apply ha,
      assumption,
    assumption
  },
  { intros b hb,
    cases' b with c,
    { rw mul_zero at hb,
      rw mul_succ at hb,
      exfalso,
      apply ha,
      rw eq_comm at hb,
      apply add_left_eq_zero hb,
    },
    { congr', -- c = d -> succ c = succ d
      apply hd,
      rw mul_succ at hb,
      rw mul_succ at hb,
      apply add_right_cancel hb
    }
  }
end

end mynat
