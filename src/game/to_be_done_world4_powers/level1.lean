import game.world3.level8 -- hide
import mynat.pow
namespace mynat -- hide
-- Sian
#check pow_zero
#check pow_succ

lemma zero_pow_zero : (0 : mynat) ^ (0 : mynat) = 1 :=
begin [less_leaky]
  rw pow_zero,
  refl,


end


lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 :=
begin [less_leaky]
  rw pow_succ,
  rw mul_zero,
  refl,


end

lemma pow_one (m : mynat) : m ^ (1 : mynat) = m :=
begin [less_leaky]
  rw one_eq_succ_zero,
  rw pow_succ,
  rw pow_zero,
  rw one_mul,
  refl,

end

lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin [less_leaky]
  induction m with t ht,
    rw pow_zero,
    refl,
  rw pow_succ,
  rw ht,
  rw mul_one,
  refl,

end

lemma pow_add (m a b : mynat) : m ^ (a + b) = m ^ a * m ^ b :=
begin [less_leaky]
  induction b with t ht,
    rw [add_zero, pow_zero, mul_one],
    refl,
  rw [add_succ, pow_succ, pow_succ, ht, mul_assoc],
  refl,
end

lemma mul_pow (m n a : mynat) : (m * n) ^ a = m ^ a * n ^ a :=
begin
  induction' a with t Ht,
    rw' [pow_zero, pow_zero, pow_zero, mul_one],
    refl,
  rw' [pow_succ, pow_succ, pow_succ, Ht],

end

lemma pow_mul (m a b : mynat) : m ^ (a * b) = (m ^ a) ^ b :=
begin
  induction' b with t Ht,
    rw' [mul_zero, pow_zero, pow_zero],
    refl,
  rw' [mul_succ, pow_add, Ht, pow_succ],
  refl,
end

-- Should this be in world 3?
lemma le_mul (a b c d : mynat) : a ≤ b → c ≤ d → a * c ≤ b * d :=
begin
intros hab hcd,
cases' a with t Ht,
  rw' [zero_mul],
  apply zero_le,
have cz : 0 ≤ c,
  apply zero_le,
have bz : 0 ≤ b,
  apply zero_le,
apply mul_le_mul hab hcd cz bz,
end

--End of world 3

lemma pow_le (m n a : mynat) : m ≤ n → m ^ a ≤ n ^ a :=
begin
intro h,
induction' a with t Ht,
  rw' [pow_zero, pow_zero],
  refl,
rw' [pow_succ, pow_succ],
apply le_mul,
  assumption,
assumption,
end

end mynat
