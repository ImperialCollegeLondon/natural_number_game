import game.level2.page2
import mynat.mul

namespace mynat


/-
-- goal : mul_comm. 
-- mul_comm leads to ⊢ a * d + a = succ d * a
-- so perhaps we need add_mul
-- but add_mul leads to either a+b+c=a+c+b or (a+b)+(c+d)=(a+c)+(b+d)
-- (depending on whether we do induction on b or c)
-/

/-
We will need the next lemma for commutivity of multiplication.
-/

/- Lemma
For all natural numbers $a$ and $b$, we have
$$ \operatorname{succ}(a) * b = a * b + b. $$
-/
lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin [less_leaky]
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
    rw add_right_comm,
    refl,
  }
end

/-
Turns out we don't actually need the next lemma for mul_comm.
-/

/- Lemma
Addition is distributive over multiplication.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$$ (a + b) * c = a * c + b * c. $$
-/
lemma add_mul (a b c : mynat) : (a + b) * c = a * c + b * c :=
begin [less_leaky]
  induction' b with d hd,
  { 
    rw zero_mul,
    rw add_zero,
    rw add_zero,
    refl
  },
  {
    rw add_succ,
    rw succ_mul,
    rw hd,
    rw succ_mul,
    rw add_assoc,
    refl
  }
end

def right_distrib := add_mul -- stupid field name, -- hide

def collectible_05 : semiring mynat := by structure_helper 

/- Lemma
Multiplication is commutative.
-/
lemma mul_comm (a b : mynat) : a * b = b * a :=
begin [less_leaky]
  induction' b with d hd,
  { 
    rw zero_mul,
    rw mul_zero,
    refl,
  },
  {
    rw succ_mul,
    rw ←hd,
    rw mul_succ,
    refl,
  }
end

def collectible_06 : comm_semiring mynat := by structure_helper


end mynat