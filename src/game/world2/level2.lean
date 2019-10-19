import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level1 -- hide
namespace mynat -- hide

/- 
# World 2 -- addition world

## Level 2 -- `add_assoc` -- associativity of addition.

## Your theorems:

  * `zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)`
  * `succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b`
  * `add_zero : ∀ a : mynat, a + 0 = a`
  * `add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)`
  * `zero_add : ∀ a : mynat, 0 + a = a`

See if you can prove associativity of addition. Hint: because addition was defined
by recursion on the right-most variable, use induction on the right-most
variable (try other variables at your peril!)

Reminder: you are done when you see "no goals" in the top right, and an empty
box (no errors) in the bottom right.
-/

/- Lemma
On the set of natural numbers, addition is associative.
In other words, for all natural numbers $a, b$ and $c$, we have
$$ (a + b) + c = a + (b + c). $$
-/
lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin [less_leaky]
  induction c with d hd,
  { -- ⊢ a + b + 0 = a + (b + 0)
    rw add_zero,
    rw add_zero,
    refl
  },
  { -- ⊢ (a + b) + succ d = a + (b + succ d)
    rw add_succ,
    rw add_succ,
    rw add_succ,
    rw hd,
    refl,
  }
end

/-
Once you have associativity (sub-boss), let's move on to commutativity (boss).
-/
end mynat -- hide 

