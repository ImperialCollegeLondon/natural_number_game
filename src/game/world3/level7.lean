import game.world3.level6 -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 7: `add_mul`

We proved `mul_add` already, but because we don't have commutativity yet
we also need to prove `add_mul`. Now we have `succ_mul` this won't
be too hard.
-/

/- Lemma
Addition is distributive over multiplication.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$$ (a + b) * t = a * t + b * t. $$
-/
lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin [less_leaky]
  induction b with d hd,
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

/-
A mathematician would now say that you have proved that the natural
numbers are a semiring.
-/

def right_distrib := add_mul -- stupid field name, -- hide

def collectible_05 : semiring mynat := by structure_helper  -- hide

end mynat -- hide
