import mynat.definition -- Imports the natural numbers.

/- Here's what you get from the import:

1) The following data:
  * a type called `mynat`
  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after n".

2) The following axioms:
  * `zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)`, the statement that zero isn't a successor.
  -- this ensures that there is more than one natural number.
  * `succ_inj : ∀ {a b : mynat}, succ(a) = succ(b) → a = b`, the statement that
     if succ(a) = succ(b) then a = b.
  -- this ensures that there are infinitely many natural numbers.

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

-- 
example : (1 : mynat) + 1 = 2 :=
begin
  refl
end

lemma zero_add (n : mynat) : 0 + n = n :=
begin
  induction n with d hd,
  tidy_zeros,
  {
    rw' add_zero,
    refl,
  },
  { rw' add_succ,
    rw' hd,
    refl
  }
end

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
  induction c with d hd,
  tidy_zeros,
  { -- ⊢ a + b + 0 = a + (b + 0)
    rw' add_zero,
    rw' add_zero,
    refl
  },
  { -- ⊢ (a + b) + succ d = a + (b + succ d)
    rw' add_succ,
    rw' add_succ,
    rw' add_succ,
    rw' hd,
    refl,
  }
end

-- first point: needs add_assoc, zero_add, add_zero
instance : add_monoid mynat := by structure_helper

-- failed attempt to prove add_comm because we 
-- are going too fast.

-- isolate independent useful thing and prove it first
lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin
  induction b with d hd,
  tidy_zeros,
  {
    refl
  }, 
  { rw' add_succ,
    rw' hd,
    rw' add_succ,
    refl
  }
end

lemma add_comm (a b : mynat) : a + b = b + a :=
begin
  induction b with d hd,
  tidy_zeros,
  { -- ⊢ a + 0 = 0 + a,
    rw' zero_add,
    rw' add_zero,
    refl
  },
  {
    rw' add_succ,
    rw' hd,
    rw' succ_add,
    refl
  }
end

-- level up
instance : add_comm_monoid mynat := by structure_helper

-- extra stuff which will not give us any 

-- TODO PR
attribute [symm] ne.symm

theorem succ_ne_zero : ∀ {{a : mynat}}, succ a ≠ 0 := 
begin
  intro a,
  symmetry,
  exact zero_ne_succ a,
end


theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
begin
  split,
  { exact succ_inj},
  { intro H,
    rw' H,
    refl,
  }
end

theorem add_left_cancel ⦃ a b c : mynat⦄ : a + b = a + c → b = c :=
begin
  intro h,
  rw' add_comm at h,
  rw' add_comm a at h,
  revert b c,
  induction a with d hd,
  change mynat.zero with 0 at *,
  { intros b c,
    intro h,
    rw add_zero at h,
    rw add_zero at h,
    assumption
  },
  { intros b c,
    intro h,
    rw add_succ at h,
    rw add_succ at h,
    rw ←succ_add at h,
    rw ←succ_add at h,
    apply succ_inj,
    exact hd h
  }
end

theorem add_right_cancel ⦃a b c : mynat⦄ : a + b = c + b → a = c :=
begin
  intro h,
  rw add_comm at h,
  rw add_comm c at h,
  exact add_left_cancel h
end


theorem add_right_cancel_iff (a b t : mynat) :  a = b ↔ a + t = b + t :=
begin
  split,
  { intro H, -- H : a = b,
    rw' H,
    refl,
  },
  { apply add_right_cancel }
end

-- this is used for antisymmetry of ≤
lemma eq_zero_of_add_right_eq_self {{a b : mynat}} : a + b = a → b = 0 :=
begin
  intro h,
  induction a with a ha,
  tidy_zeros,
  { 
    rw' zero_add at h,
    assumption
  },
  { apply ha,
    apply succ_inj,
    rw' succ_add at h,
    assumption,
  }
end

-- now used for antisymmetry of ≤
lemma add_left_eq_zero {{a b : mynat}} : a + b = 0 → b = 0 :=
begin
  intro H,
  cases b with c,
  all_goals {try {change mynat.zero with (0 : mynat) at *}},
  { refl},
  { rw add_succ at H,
    exfalso,
    apply zero_ne_succ (a + c),
    rw' H,
    refl,
  },
end

lemma add_right_eq_zero {{a b : mynat}} : a + b = 0 → a = 0 :=
begin
  intro H,
  rw' add_comm at H,
  exact add_left_eq_zero H,
end
theorem one_eq_succ_zero : (1 : mynat) = succ 0 :=
begin
  refl,
end

theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin
  rw one_eq_succ_zero,
  rw add_succ,
  rw' add_zero,
  refl,
end

end mynat