import world1_addition_solutions

namespace mynat

def mul : mynat → mynat → mynat
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul mynat := ⟨mul⟩
-- notation a * b := mul a b

example : (1 : mynat) * 1 = 1 := 
begin
refl
end

lemma mul_zero (m : mynat) : m * 0 = 0 := rfl

lemma mul_succ (m n : mynat) : m * (succ n) = m * n + m := rfl

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
  induction b with d hd,
  { 
    -- leaky zero
    show (a + 0) * c = a * c + 0 * c,
    rw zero_mul,
    rw add_zero,
    rw add_zero,
  },
  {
    rw add_succ,
--    change succ (a + d) * c = _,
    rw succ_mul,
    rw hd,
    rw succ_mul,
    rw add_assoc
  }
end

def right_distrib := add_mul -- stupid field name, 

lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
  induction b with d hd,
  { -- leakage
    show a * 0 = 0 * a,
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
  -- hab : succ (succ a * b + a) = zero
  cases hab, -- HARD: proof that succ a = 0 -> contradiction
end

-- goal is comm_semiring
--set_option pp.all true
instance : comm_semiring mynat := by structure_helper

end mynat
