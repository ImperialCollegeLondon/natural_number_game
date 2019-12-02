import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level3 -- hide
namespace mynat -- hide

/- 
# Addition World

## Level 4: `add_comm` (boss level)

[boss battle music]

Look in Theorem statements -> Addition world to see the proofs you have.
These should be enough.
-/

/- Lemma
On the set of natural numbers, addition is commutative.
In other words, for all natural numbers $a$ and $b$, we have
$$ a + b = b + a. $$
-/
lemma add_comm (a b : mynat) : a + b = b + a :=
begin [nat_num_game]
  induction b with d hd,
  { rw zero_add,
    rw add_zero,
    refl
  },
  { rw add_succ,
    rw hd,
    rw succ_add,
    refl
  }
end

/-

If you got this far -- nice! You're nearly ready to make a choice:
Multiplication World or Function World. But there are just a couple
more useful lemmas in Addition World which you should prove first.
Press on to level 5.

-/
end mynat -- hide 
