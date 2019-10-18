import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level4 -- hide
namespace mynat -- hide

/-
These are some more advanced facts about addition. To be quite
frank I'm not even sure I've explained enough about Lean for them
to be possible. Try some of them; let me know which ones are
really hard, and I'll try to fix them up.

If you just want to skip these and move straight on to multiplication,
click on "next level" on the top right (and then click on "previous page"
  a few times to get you back to Level 3 Page 1 -- sorry ;-) )
-/

/- Theorem
Zero is not the successor of any natural number.
-/
theorem succ_ne_zero : ∀ {{a : mynat}}, succ a ≠ 0 := 
begin [less_leaky]
  intro a,
  symmetry,
  exact zero_ne_succ a,
end

/- Theorem
Two natural numbers are equal if and only if their successors are equal.
-/
theorem eq_iff_succ_eq_succ (a b : mynat) : succ a = succ b ↔ a = b :=
begin [less_leaky]
  split,
  { exact succ_inj},
  { intro H,
    rw H,
    refl,
  }
end

/- Theorem
For any natural number $n$, we have
$$ \operatorname{succ}(n) = n+1. $$
-/
theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin [less_leaky]
  rw one_eq_succ_zero,
  rw add_succ,
  rw add_zero,
  refl,
end


/- Lemma
For all natural numebrs $a, b$ and $c$, we have
$$ a + b + c = a + c + b. $$
-/
lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin [less_leaky]
  rw add_assoc,
  rw add_comm b c,
  rw ←add_assoc,
  refl,
end

/- Theorem
On the set of natural numbers, addition has the left cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + b = a + c, $$
then we have $b = c$.
-/
theorem add_left_cancel ⦃ a b c : mynat⦄ : a + b = a + c → b = c :=
begin [less_leaky]
  intro h,
  rw add_comm at h,
  rw add_comm a at h,
  revert b c,
  induction a with d hd,
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

/- Theorem
On the set of natural numbers, addition has the right cancellation property.
In other words, if there are natural numbers $a, b$ and $c$ such that
$$ a + b = c + b, $$
then we have $a = c$.
-/
theorem add_right_cancel ⦃a b c : mynat⦄ : a + b = c + b → a = c :=
begin [less_leaky]
  intro h,
  rw add_comm at h,
  rw add_comm c at h,
  exact add_left_cancel h
end

theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=
begin [less_leaky]
  split,
  { apply add_right_cancel}, -- done that way already,
  { intro H, -- H : a = b,
    rw H,
    refl,
  }
end

/-
The following lemma will be useful when we want to prove that $\leq$ is antisymmetric.
-/

/- Lemma
If $a$ and $b$ are natural numbers such that 
$$ a + b = a, $$
then $b = 0$.
-/
lemma eq_zero_of_add_right_eq_self {{a b : mynat}} : a + b = a → b = 0 :=
begin [less_leaky]
  intro h,
  induction a with a ha,
  { 
    rw zero_add at h,
    assumption
  },
  { apply ha,
    apply succ_inj,
    rw succ_add at h,
    assumption,
  }
end

/- Lemma
If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $b = 0$.
-/
lemma add_left_eq_zero {{a b : mynat}} : a + b = 0 → b = 0 :=
begin [less_leaky]
  intro H,
  cases b with c,
  { refl},
  { rw add_succ at H,
    exfalso,
    apply zero_ne_succ (a + c),
    rw H,
    refl,
  },
end

/- Lemma
If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $a = 0$.
-/
lemma add_right_eq_zero {{a b : mynat}} : a + b = 0 → a = 0 :=
begin [less_leaky]
  intro H,
  rw add_comm at H,
  exact add_left_eq_zero H,
end

/- Theorem
For any natural number $d$, we have
$$ d+1 = \operatorname{succ}(d). $$
-/
theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin [less_leaky]
  rw succ_eq_add_one,
  refl,
end

/- Lemma
For any natural number $n$, we have
$$ n \neq \operatorname{succ}(n). $$
-/
lemma ne_succ_self (n : mynat) : n ≠ succ n :=
begin [less_leaky]
  induction n with d hd,
    apply zero_ne_succ,
  intro hs,
  apply hd,
  apply succ_inj,
  assumption
end

end mynat
