import mynat.definition -- Imports the natural numbers.

/- 
Here's what you get from this import:

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

/- 
Here's what you get from the import:

1) The following data:
  * a function called mynat.add, and notation a + b for this function

2) The following axioms:

  * `add_zero : ∀ a : mynat, a + 0 = a`
  * `add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)`

These axiom between them tell you how to work out a + x for every x; use induction on x to
reduce to the case either `x = 0` or `x = succ b`, and then use `add_zero` or `add_succ` appropriately.
-/

namespace mynat

/-
-- Summary:

-- Naturals:
-- 1) 0 and succ are constants
-- 2) succ_inj and zero_ne_succ are axioms
-- 3) Induction works.

-- Addition:
-- 1) add_zero and add_succ are the axioms
-- 2) notation is a + b
-/

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

end mynat