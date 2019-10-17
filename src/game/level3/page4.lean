import game.level2.page3 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/- Theorem
Multiplication of two non-zero natural numbers is non-zero.
-/
theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin [less_leaky]
  intros ha hb,
  intro hab,
  cases b with b,
    apply hb,
    refl,
  rw mul_succ at hab,
  apply ha,
  cases a with a,
    refl,
  rw add_succ at hab,
  exfalso,
  apply succ_ne_zero hab
end

/-
This involves a lot of cases. Would be really cool
 to have some sort of trickery instead of all the {}s.
-/

/- Theorem
If $a * b = 0$, if and only if at least one of $a$ or $b$ is equal to zero.
-/
theorem mul_eq_zero_iff : ∀ (a b : mynat), a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin [less_leaky]
  intros a b,
  split, swap,
    intro hab, cases hab,
      rw hab, rw zero_mul, refl,
    rw hab, rw mul_zero, refl,
  intro hab,
  cases a with d,
    left, refl,
  cases b with e he,
    right, refl,
  exfalso,
  rw mul_succ at hab,
  rw add_succ at hab,
  exact succ_ne_zero hab,
end

/- Theorem
If $a * b = 0$, then at least one of $a$ or $b$ is equal to zero.
-/
theorem eq_zero_or_eq_zero_of_mul_eq_zero ⦃a b : mynat⦄ (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin [less_leaky]
  revert a,
  induction b with c hc,
  { intros a ha,
    right, refl,
  },
  { intros a ha,
    rw mul_succ at ha,
    left,
    apply add_left_eq_zero ha
  }
end

-- instance : comm_semiring mynat := by structure_helper -- hide

/-
The next theorem may be useful in the next level.
-/

/- Theorem
If $a \neq 0$, $b$ and $c$ are natural numbers such that
$$ a * b = a * c, $$
then $b = c$.
-/
theorem mul_left_cancel ⦃a b c : mynat⦄ (ha : a ≠ 0) : a * b = a * c → b = c :=
begin [less_leaky]
  revert b,
  induction c with d hd,
  { intro b,
    rw mul_zero,
    intro h,
    cases (eq_zero_or_eq_zero_of_mul_eq_zero h),
      exfalso,
      apply ha,
      assumption,
    assumption
  },
  { intros b hb,
    cases b with c,
    { rw mul_zero at hb,
      rw mul_succ at hb,
      exfalso,
      apply ha,
      rw eq_comm at hb,
      apply add_left_eq_zero hb,
    },
    { congr, -- c = d -> succ c = succ d
      apply hd,
      rw mul_succ at hb,
      rw mul_succ at hb,
      apply add_right_cancel hb
    }
  }
end

/- To come: inequalities! Exponentiation! Odd and even numbers! Congruences!
Prime numbers! And any other mathematics with the natural numbers that anyone can think of. 
Suggestions welcome to k.buzzard@imperial.ac.uk . Many many thanks to Mohammad Pedramfar
for writing the web interface.

-/

end mynat -- hide