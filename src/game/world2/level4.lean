import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level3 -- hide
namespace mynat -- hide

/- 
# World 2 -- Addition world

## Level 4 (boss level) : `add_comm`

You are equipped with:

  * `add_zero (a : mynat) : a + 0 = a`
  * `add_succ (a b : mynat) : a + succ(b) = succ (a + b)`
  * `zero_add (a : mynat) : 0 + a = a`
  * `add_assoc (a b c : mynat) : (a + b) + c = a + (b + c)`
  * `succ_add (a b : mynat) : succ a + b = succ (a + b)`

[boss battle music]
-/

/- Lemma
On the set of natural numbers, addition is commutative.
In other words, for all natural numbers $a$ and $b$, we have
$$ a + b = b + a. $$
-/
lemma add_comm (a b : mynat) : a + b = b + a :=
begin [less_leaky]
  induction b with d hd,
  { -- ⊢ a + 0 = 0 + a,
    rw zero_add,
    rw add_zero,
    refl
  },
  {
    rw add_succ,
    rw hd,
    rw succ_add,
    refl
  }
end

/-

If you got this far -- nice! You're nearly ready to go onto
multiplication world. There are just a couple more useful lemmas
which you should prove first. Press on to level 5.

-/
end mynat -- hide 
