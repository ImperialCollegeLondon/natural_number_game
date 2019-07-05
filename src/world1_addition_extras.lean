import world1_addition_core

namespace mynat

-- nobody wants to see pred. 
--def pred : mynat → mynat
--| zero := zero
--| (succ n) := n

-- I needed succ_inj for the ∃ c, a + c = b definition of ≤
-- lemma succ_inj {a b : mynat} : succ a = succ b → a = b :=

theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
begin
split,
{ exact succ_inj},
{ intro H,
  rw H}
end

theorem add_cancel_right (a b t : mynat) :  a = b ↔ a + t = b + t :=
begin
  split,
  { intro H, -- H : a = b,
    rw H,
  },
  { intro P,
    induction t with d Hd,
    { exact P},
    { rw add_succ at P,
      rw add_succ at P,
      apply Hd,
      apply succ_inj,
      assumption
    }, 
  }
end

lemma eq_zero_of_add_right_eq_self (a b : mynat) : a + b = a → b = 0 :=
begin
  intro h,
  induction a with a ha,
  { change 0 + b = 0 at h, -- leakage
    rw zero_add at h,
    assumption
  },
  { apply ha,
    apply succ_inj,
    rw succ_add at h,
    assumption,
  }
end

end mynat