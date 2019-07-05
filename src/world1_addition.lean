import mynat.definition -- Imports the natural numbers.

/- Here's what you get from the import:

1) The following data:
  * a type called `mynat`
  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after n".

2) The following axioms:
  * `zero_ne_succ : ∀ a : mynat, zero ≠ succ(a)`, the statement that zero isn't a successor.
  -- this ensures that there is more than one natural number.
  * `succ_inj : ∀ (a b : mynat), succ(a) = succ(b) → a = b`, the statement that if succ(a) = succ(b) then a = b.
  -- this ensures that there are infinitely many.

3) The principle of mathematical induction.

  * In practice this means that if you have `n : mynat` then you can use the tactic `induction n`.

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


example : (1 : mynat) + 1 = 2 :=
begin
  sorry
end

lemma zero_add (n : mynat) : 0 + n = n :=
begin
  induction n with d hd,
  {
    show (0 : mynat) + 0 = 0, -- THIS LINE SHOULD NOT BE SEEN
    rw add_zero,
  },
  { rw add_succ,
    rw hd,
  }
end

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
  induction c with d hd,
  { -- (a + b) + zero = a + (b + zero)
   -- I don't want leakage of nat.zero. I want to stick to has_zero.zer
    show a + b + 0 = a + (b + 0),
    rw add_zero,
    rw add_zero, -- goal goes 
  },
  { -- (a + b) + succ d = a + (b + succ d)
    rw add_succ,
    rw add_succ,
    rw add_succ,
    rw hd,
  }
end

-- level up
-- #print add_monoid
/-
class add_monoid α extends add_semigroup α :=
(zero_add : ∀ a : α, 0 + a = a) (add_zero : ∀ a : α, a + 0 = a)

-/
-- Lean should automatically generate this proof from my naming conventions.
-- i.e.
-- instance : add_monoid my_nat := by common_sense
instance : add_monoid mynat := by i_checked_all_teh_axioms

-- For pedagogical reasons I would like to make this structure
-- at this point, not when making add_comm_monoid (we are a long
-- way from add_comm)

instance : add_semigroup mynat := by apply_instance

lemma add_one (n : mynat) : n + 1 = succ n :=
begin
  refl
end

lemma one_add (n : mynat) : 1 + n = succ n :=
begin
  induction n with d hd,
  {
    refl
  },
  { rw add_succ,
    rw hd
  }
end

-- failed attempt to prove add_comm because we 
-- are going too fast.

-- isolate independent useful thing and prove it first
lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin
  induction b with d hd,
  {
    refl
  }, 
  { rw add_succ,
    rw hd,
    refl
  }
end

lemma add_comm (a b : mynat) : a + b = b + a :=
begin
  induction b with d hd,
  { -- leaky zero
    show a + 0 = 0 + a,
    rw zero_add,
    rw add_zero
  },
  {
    rw add_succ,
-- or    show succ (a + d) = _,
    rw hd,
    rw succ_add,
  }
end

-- level up

/-
class add_comm_semigroup X extends add_semigroup X :=
(add_comm : ∀ a b : X, a + b = b + a)
-/
instance : add_comm_semigroup mynat := by i_checked_all_teh_axioms

-- class add_comm_monoid (α : Type u) extends add_monoid α, add_comm_semigroup α
instance : add_comm_monoid mynat := by i_checked_all_teh_axioms

end mynat