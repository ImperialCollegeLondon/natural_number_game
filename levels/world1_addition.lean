import mynat.definition -- Imports the natural numbers.

/- Here's what you get from the import:

1) The following data:
  * a type called `mynat`
  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after n".
  * Usual numerical notation 0,1,2,3,4,5 etc.

2) The following axioms:
  * `zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)`, the statement that zero isn't a successor.
  -- this ensures that there is more than one natural number.
  * `succ_inj : ∀ {a b : mynat}, succ(a) = succ(b) → a = b`, the statement that
     if succ(a) = succ(b) then a = b.
  -- this ensures that there are infinitely many natural numbers.

3) The principle of mathematical induction.

  * In practice this means that if you have `n : mynat` then you can use the tactic `induction n`.

4) A few useful extra things:

  * The theorem `one_eq_succ_zero : 1 = succ 0`
  * The theorem `ne_iff_implies_false : a ≠ b ↔ (a = b) → false`

-/

import mynat.add -- definition of addition

/- Here's what you get from the import:

1) The following data:
  * a function called mynat.add, and notation a + b for this function

2) The following axioms:

  * `add_zero : ∀ a : mynat, a + 0 = a`
  * `add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)`

These axiom between them tell you how to work out a + x for every x; use induction on x to
reduce to the case either `x = 0` or `x = succ b`, and then use `add_zero` or `add_succ` appropriately.
-/

namespace mynat

-- Summary:

-- Naturals:
-- 1) 0 and succ are constants
-- 2) succ_inj and zero_ne_succ are axioms
-- 3) Induction works.

-- Addition:
-- 1) add_zero and add_succ are the axioms
-- 2) notation is a + b

/-
 Collectibles in this level:

add_comm_monoid -- collectible_02
  add_monoid [zero_add] -- collectible_01
    (has_zero)
    add_semigroup [add_assoc]
      (has_add)
  add_comm_semigroup [add_comm]
    add_semigroup (see above)
-/

/-
Instructions: First carefully explain definition of nat and add. Then
guide them through the first level. 

"We're going to prove this by induction on n, which is a natural
thing to do because we defined addition by recursion on n (you
prove things by induction and define them by recursion).

For the base case, we are going to use the axiom that a + 0 = 0.
refl closes a goal of the form x = x. how to use add_succ here?

etc.

Full solution to zero_add:

  induction n with d hd,
    rw add_zero,
    refl,
  rw add_succ,
  rw hd,
  refl,

"
-/

lemma zero_add (n : mynat) : 0 + n = n :=
begin [nat_num_game]
  sorry
end

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin [nat_num_game]
  sorry
end

-- first point: needs add_assoc, zero_add, add_zero
def collectible_01 : add_monoid mynat := by structure_helper
--#print axioms collectible_01 -- prove you got this by uncommenting

-- proving add_comm immediately is still tricky; trying it
-- reveals a natural intermediate lemma which we prove first.

lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin [nat_num_game]
  sorry
end

lemma add_comm (a b : mynat) : a + b = b + a :=
begin [nat_num_game]
  sorry
end

-- level up
def collectible_02 : add_comm_monoid mynat := by structure_helper
--#print axioms collectible_02

-- no more collectibles beyond this point in this file, however
-- stuff below is used in other collectibles in other files.

theorem succ_ne_zero : ∀ {{a : mynat}}, succ a ≠ 0 := 
begin [nat_num_game]
  sorry
end

theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
begin [nat_num_game]
  sorry
end

theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin [nat_num_game]
  sorry
end

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin [nat_num_game]
  sorry
end

theorem add_left_cancel ⦃ a b c : mynat⦄ : a + b = a + c → b = c :=
begin [nat_num_game]
  sorry
end

theorem add_right_cancel ⦃a b c : mynat⦄ : a + b = c + b → a = c :=
begin [nat_num_game]
  sorry
end

theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=
begin [nat_num_game]
  sorry
end

-- this is used for antisymmetry of ≤
lemma eq_zero_of_add_right_eq_self {{a b : mynat}} : a + b = a → b = 0 :=
begin [nat_num_game]
  sorry
end

-- now used for antisymmetry of ≤
lemma add_left_eq_zero {{a b : mynat}} : a + b = 0 → b = 0 :=
begin [nat_num_game]
  sorry
end

lemma add_right_eq_zero {{a b : mynat}} : a + b = 0 → a = 0 :=
begin [nat_num_game]
  sorry
end

theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin [nat_num_game]
  sorry
end

def ne_succ_self (n : mynat) : n ≠ succ n :=
begin [nat_num_game]
  sorry
end

end mynat