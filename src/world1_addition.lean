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

Note also 

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

  add_monoid
  --add_assoc
  --zero_add
  --add_zero

add_comm_monoid
  (add_monoid)
  --add_comm
-/

lemma zero_add (n : mynat) : 0 + n = n :=
begin [less_leaky]
  --cases n with d, -- no leaks
  induction n with d hd, -- no leaks
    rw add_zero, -- doesn't close goals.
    refl,
  rw add_succ,
  rw hd,
  refl,
end
-- all compiles

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
  sorry
end

-- first point: needs add_assoc, zero_add, add_zero
instance : add_monoid mynat := by structure_helper

-- Trying to prove add_comm directly now results in
-- spotting an independent easier lemma which should
-- be proved first.

-- isolate independent useful thing and prove it first
lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin
  sorry
end

lemma add_comm (a b : mynat) : a + b = b + a :=
begin
  sorry
end

-- level up
instance : add_comm_monoid mynat := by structure_helper

-- extra stuff which will not give us any more instances

theorem succ_ne_zero : ∀ {{a : mynat}}, succ a ≠ 0 := 
begin
  sorry
end

theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
begin
  sorry
end

theorem add_left_cancel ⦃ a b c : mynat⦄ : a + b = a + c → b = c :=
begin
  sorry
end

theorem add_right_cancel ⦃a b c : mynat⦄ : a + b = c + b → a = c :=
begin
  sorry
end


theorem add_right_cancel_iff (a b t : mynat) :  a = b ↔ a + t = b + t :=
begin
  sorry
end

-- this is used for antisymmetry of ≤
lemma eq_zero_of_add_right_eq_self {{a b : mynat}} : a + b = a → b = 0 :=
begin
  sorry
end

-- now used for antisymmetry of ≤
lemma add_left_eq_zero {{a b : mynat}} : a + b = 0 → b = 0 :=
begin
  sorry
end

lemma add_right_eq_zero {{a b : mynat}} : a + b = 0 → a = 0 :=
begin
  sorry
end

theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin
  sorry
end

end mynat