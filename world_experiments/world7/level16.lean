import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level15 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 16/16 -- `ne_succ_self`

This isn't too hard.
-/

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

end mynat -- hide
