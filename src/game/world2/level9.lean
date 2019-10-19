import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level8 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 9 -- `add_left_cancel`

You have these:

  * zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)
  * succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b
  * add_zero : ∀ a : mynat, a + 0 = a
  * add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)
  * zero_add : ∀ a : mynat, 0 + a = a`
  * add_assoc : ∀ a b c : mynat, (a + b) + c = a + (b + c)
  * succ_add : ∀ a b : mynat, succ a + b = succ (a + b)
  * add_comm : ∀ a b : mynat, a + b = b + a

`add_left_cancel` is the theorem that you can cancel on the left
when you're doing addition -- if `a + b = a + c` then `b = c`. 
You will need to know about `intro`, `revert` and `apply`. 
Read about them in the 
<a href="http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html" target="blank">tactic guide</a>.


-/


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

end mynat -- hide