import tactic.interactive tactic.ring

inductive is_even : ℕ → Prop
| zero : is_even 0
| step {n} : is_even n → is_even (n + 2)

example : is_even 4 :=
begin
repeat { apply is_even.step },
apply is_even.zero,
end

example : ¬ is_even 5 :=
begin
intro even_five,
cases even_five with _ even_three,
cases even_three with _ even_one,
cases even_one,
end

lemma even_if_double {n} : is_even (2*n) :=
begin
induction n with d hd,
{ exact is_even.zero },
{ show is_even (2 * (d + 1)),
  rw mul_add,
  apply is_even.step,
  assumption,
 },
end

lemma double_if_even {n} : is_even n → ∃ m, n = 2*m :=
begin
intro h, induction h with d Hd ih,
{ use 0,
  refl
},
{ cases ih with n Hn,
  use (n + 1),
  rw Hn,
  refl,
 }
end

lemma even_iff_double {n} : is_even n ↔ ∃ m, n = 2*m :=
begin
split, apply double_if_even,
intro h, cases h with d Hd, rw Hd, 
  apply even_if_double
end

inductive is_odd : ℕ → Prop
| one : is_odd 1
| step {n} : is_odd n → is_odd (n + 2)

lemma odd_iff_double_add_one {n} : is_odd n ↔ ∃ m, n = 2*m + 1 :=
sorry

lemma even_of_not_odd : ∀ n, 
¬ is_odd n → is_even n
| 0 h := is_even.zero
| 1 h := begin exfalso, apply h, constructor end
| (n+2) h :=
  have ih : _, from even_of_not_odd n,
  begin
  constructor,
  apply ih,
  intro hn,
  apply h,
  constructor, assumption,
  end

#print even_of_not_odd

lemma not_odd_of_even : ∀ n, is_even n → ¬ is_odd n :=
begin
intros n h,
induction h with m m hm,
{intro h, cases h},
{intro h, apply hm, cases h, assumption},
end

lemma even_iff_not_odd : ∀ n, is_even n ↔ ¬ is_odd n :=
begin
intro n, split, apply not_odd_of_even, apply even_of_not_odd
end

lemma odd_square (n : ℕ) : is_odd n → is_odd (n*n) :=
begin
simp [odd_iff_double_add_one],
intro m,
intros  h,
use 2*m + 2*m*m, subst h, ring,
end

lemma even_square (n : ℕ) : is_even (n*n) → is_even n :=
begin
conv in (is_even (n*n)) { simp [even_iff_not_odd] },
simp [even_iff_not_odd],
intros h1 h2, apply h1,
apply odd_square, assumption
end

set_option pp.all true
#check (7 : ℤ)