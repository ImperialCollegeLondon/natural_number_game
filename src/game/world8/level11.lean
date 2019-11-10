import game.world8.level8 -- hide
namespace mynat -- hide

/-
# Advanced Addition World

## Level 8: `add_left_eq_zero`

The following lemma will also be useful in inequality world.
-/

/- Lemma
If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $b = 0$.
-/
lemma add_left_eq_zero {a b : mynat} (H : a + b = 0) : b = 0 :=
begin [less_leaky]
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
