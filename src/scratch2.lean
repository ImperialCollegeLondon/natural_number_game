inductive mynat
| zero : mynat
| succ : mynat → mynat

-- I want to never see mynat.zero again
instance : has_zero mynat := ⟨mynat.zero⟩

namespace mynat

definition add : mynat → mynat → mynat
| n 0 := n
| n (succ p) := succ (add n p)

instance : has_add mynat := ⟨mynat.add⟩

theorem zero_add : ∀ x : mynat, 0 + x = x :=
begin
  intro x,
  induction x with d hd,
  { -- ⊢ 0 + zero = zero -- leakage of "zero" i.e. mynat.zero
    sorry
  },
  { -- inductive case is fine
    sorry
  }
end

/-
⊢ @eq.{1} mynat (@has_add.add.{0} mynat mynat.has_add (@has_zero.zero.{0} mynat mynat.has_zero) mynat.zero) mynat.zero
-/


theorem one_add_one_equals_two : one + one = two :=
begin
unfold two,
unfold one,
unfold add,
end

definition three := succ two
definition four:= succ three

theorem two_add_two_equals_four : two + two = four :=
begin
refl
end

theorem add_zero (n : mynat) : n + zero = n :=
begin
unfold add
end

theorem zero_add (n : mynat) : zero + n = n :=
begin
induction n with d Hd,
{ refl,},
{ show succ (zero + d) = succ d,
    rewrite Hd,
},
end

theorem add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
induction c with t Ht,
   refl,
unfold add,
rewrite Ht,
end

theorem zero_add_eq_add_zero (n : mynat) : zero + n = n + zero :=
begin
rewrite [zero_add, add_zero],
end

theorem add_one_eq_succ (n : mynat) : n + one = succ n :=
begin
unfold one,
unfold add,
end

theorem one_add_eq_succ (n : mynat) : one + n = succ n :=
begin
unfold one,
induction n with t Ht,
  refl,
unfold add,
rewrite Ht,
end

theorem add_comm (a b : mynat) : a + b = b + a :=
begin
induction b with t Ht,
rw[zero_add_eq_add_zero],
unfold add,
rw [Ht, ←one_add_eq_succ, ←add_assoc, one_add_eq_succ], -- how do you make the arrow
end

theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
begin
split,
  exact succ.inj, -- don't really understand exact command
assume H : a = b,
rw [H]
end

theorem add_cancel_right (a b t : mynat) :  a = b ↔ a+t = b+t :=
begin
split,
assume J : a=b,
induction t with s Hs,
rw[add_zero, J, add_zero], -- base case of a=b implies
unfold add,
rw Hs, -- inductive case of a=b implies
induction t with r Hr,
unfold add,
assume K : a=b, -- bit iffy cause I'm assuming what I'm proving but I got to a=b->a=b and wasn't sure why it wasn't goal complete?
rw K, -- base case of a+t=b+t implies
unfold add,
rw[eq_iff_succ_eq_succ],
assumption
end

open nat

example (P : ℕ → Prop) (n : ℕ) : P n :=
begin
  induction n with d hd,
end 
end xena