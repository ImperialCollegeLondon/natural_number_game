import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level11 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 12 -- `eq_zero_of_add_right_eq_self`

You have : the usual stuff. 

  * `succ_inj (a b : mynat) : succ(a) = succ(b) → a = b`

will be useful for this one. 

You might want to read about how `rw zero_add at h` works in the
<a href="http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html" target="blank">tactic guide</a>.

The lemma you're about to prove will be useful when we want to prove that $\leq$ is antisymmetric.
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

end mynat -- hide
