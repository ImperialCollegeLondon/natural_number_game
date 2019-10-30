import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level4 -- hide
namespace mynat -- hide

/- Axiom : one_eq_succ_zero
1 = succ(0)
-/

/-

# World 2 -- Addition World

## Level 5 -- `succ_eq_add_one`

You have these:

  * `add_zero (a : mynat) : a + 0 = a`
  * `add_succ (a b : mynat) : a + succ(b) = succ(a + b)`
  * `zero_add (a : mynat) : 0 + a = a`
  * `add_assoc (a b c : mynat) : (a + b) + c = a + (b + c)`
  * `succ_add (a b : mynat) : succ a + b = succ (a + b)`
  * `add_comm (a b : mynat) : a + b = b + a`
  * `one_eq_succ_zero : 1 = succ(0)`
-/

/-
Levels 5 and 6 are the two last levels in this world
which you should really do before you go on to multiplication world.
Level 5 involves the number 1. The theorem that 1 = succ(0) is called

`one_eq_succ_zero : 1 = succ(0)`

and you've had it all along -- we just never needed it yet.
When you see a 1 in your goal,
you can write `rw one_eq_succ_zero` to get back
to something which only mentions `0`. This is a good move because 0 is easier to
manipulate than 1 right now, because you have
some theorems about 0 (`zero_add`, `add_zero`) and other than `1 = succ(0)`,
no theorems at all which mention 1. Let's prove one now.
-/

/- Theorem
For any natural number $n$, we have
$$ \operatorname{succ}(n) = n+1. $$
-/
theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin [less_leaky]
  rw one_eq_succ_zero,
  rw add_succ,
  rw add_zero,
  refl,
end

end mynat -- hide
