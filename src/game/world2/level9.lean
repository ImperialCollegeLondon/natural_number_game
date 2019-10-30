import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level8 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 9 -- `add_left_cancel`

The theorem `add_left_cancel` is the theorem that you can cancel on the left
when you're doing addition -- if `a + b = a + c` then `b = c`. 
You will need to know about `intro`, `revert` and `apply`. 
Read about them in the 
<a href="http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html" target="blank">tactic guide</a>.
Briefly: `intro h` changes `⊢ P → Q` to `h : P` and `⊢ Q` -- it's the Lean analogue of "to prove P → Q, assume P is true;
now we only have to prove Q". `revert h` is the opposite; given `h : P` and a goal `⊢ Q` it deletes `h` and turns the goal back into `⊢ P → Q`. As for `apply` -- if `h : P → Q` is a hypothesis
and the goal is `⊢ Q`, then `apply h` turns the goal into `P`. There is more information about this
stuff <a href="http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/ch1_and_or_props/prop_exercises.html" target="blank">here</a>.


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
