import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level4 -- hide
namespace mynat -- hide

/- Axiom : one_eq_succ_zero
1 = succ(0)
-/

/-

# Addition World

## Level 5: `succ_eq_add_one`

I've just added `one_eq_succ_zero` (a proof of `1 = succ(0)`) to your list of theorems; this is true
by definition of $1$, but we didn't need it until now.

Levels 5 and 6 are the two last levels in Addition World.
Level 5 involves the number $1$. When you see a $1$ in your goal,
you can write `rw one_eq_succ_zero` to get back
to something which only mentions `0`. This is a good move because $0$ is easier for us to
manipulate than $1$ right now, because we have
some theorems about $0$ (`zero_add`, `add_zero`), but, other than `1 = succ(0)`,
no theorems at all which mention $1$. Let's prove one now.
-/

/- Theorem
For any natural number $n$, we have
$$ \operatorname{succ}(n) = n+1. $$
-/
theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin [nat_num_game]
  rw one_eq_succ_zero,
  rw add_succ,
  rw add_zero,
  refl,
end

end mynat -- hide
