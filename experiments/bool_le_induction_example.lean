-- random experiments that predate [less_leaky] approach

import tactic.linarith -- any import is fine

@[derive decidable_eq]
inductive mybool
| ff : mybool
| tt : mybool

namespace mybool

inductive le : mybool → mybool → Prop
| f_le_f : le ff ff 
| f_le_t : le ff tt 
| t_le_t : le tt tt

-- notation
instance : has_le mybool := ⟨mybool.le⟩

-- I now never want to see `le` ever ever again.

open le

-- Could I have generated this automatically?

instance decidable_le : ∀ a b : mybool, decidable (a ≤ b) :=
λ a b, mybool.rec_on a (mybool.rec_on b (is_true f_le_f) $ is_true f_le_t) $
  mybool.rec_on b (is_false $ λ h, by cases h) $ is_true t_le_t

instance decidable_le' : ∀ a b : mybool, decidable (a ≤ b) :=
λ a b, begin
  cases a; cases b;
    -- just work it out Lean
  try {exact is_true t_le_t};
  try {exact is_true f_le_t};
  try {exact is_true f_le_f};
  try {exact (is_false $ λ h, by cases h)}
end 

theorem induction (a b : mybool) (h : a ≤ b)  (P : Π (c d : mybool), Prop)
: P ff ff → P ff tt → P tt tt → P a b := λ h_ff_ff h_ff_tt h_tt_tt,
begin
cases a;cases b,
  exact h_ff_ff,
  exact h_ff_tt,
  cases h,
  exact h_tt_tt,
end

example (a b : mybool) (h : a ≤ b)  (P : Π (a b : mybool), Prop)
  -- possible other hypotheses here
  : P a b :=
begin
  cases a; cases b; cases h,
  -- is there a tactic of the form `thing h` which does the same thing?
  sorry, sorry, sorry
end

-- These presumably could have been auto-generated but I didn't want
-- to clog up the code with weird @isms



theorem le_refl (a : mybool) : a ≤ a :=
begin
  cases a; exact dec_trivial,
  -- Is there just one tactic which will do this?
end

theorem le_trans {a b c : mybool} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
  cases a;cases b;cases c; cases hab; cases hbc;
  exact dec_trivial,
  -- Is there just one tactic which will do this?
end


theorem le_antisymm {a b : mybool} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
begin
  cases a; cases b; cases hab; cases hba; exact dec_trivial,
  -- Is there just one tactic which will do this?
end

end mybool