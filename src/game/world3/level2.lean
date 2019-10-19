import game.world3.level1 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/- Lemma
For any natural number $m$, we have
$$ m * 1 = m. $$
-/
lemma mul_one (m : mynat) : m * 1 = m :=
begin [less_leaky]
  rw one_eq_succ_zero,
  rw mul_succ,
  rw mul_zero,
  exact zero_add m,
end

-- can use succ_eq_add_one here

/- Lemma
For any natural number $m$, we have
$$ 1 * m = m. $$
-/
lemma one_mul (m : mynat) : 1 * m = m :=
begin [less_leaky]
  induction m with d hd,
  {
    rw mul_zero,
    refl,
  },
  {
    rw mul_succ,
    rw hd,
    rw succ_eq_add_one,
    refl,
  }
end

/- Lemma
Multiplication is distributive over addition.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$$ a * (b + c) = a * b + a * c. $$
-/
lemma mul_add (a b c : mynat) : a * (b + c) = a * b + a * c :=
begin [less_leaky]
  induction c with d hd,
  { rewrite [add_zero, mul_zero, add_zero],
  },
  {
    rw add_succ,
-- or    show a * succ (b + d) = _,
    rw mul_succ,
-- or    show a * (b + d) + _ = _,
    rw hd,
    rw mul_succ,
    rw add_assoc, -- ;-)
    refl,
  }
end

def left_distrib := mul_add -- stupid field name,          -- hide
-- I just don't instinctively know what left_distrib means -- hide

/- Lemma
Multiplication is associative.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$$ (a * b) * c = a * (b * c). $$
-/
lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin [less_leaky]
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
    rw mul_add,
    refl,
  }
end

--def collectible_4 : monoid mynat := by structure_helper
--#print axioms collectible_4

end mynat -- hide
