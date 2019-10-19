import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level12 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 13 -- `add_left_eq_zero`

You have the usual stuff. 

  * `zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)`

might be useful for this one.

The following lemma will be useful when we want to prove that $\leq$ is antisymmetric
somewhere in world 4.
-/

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

end mynat -- hide
