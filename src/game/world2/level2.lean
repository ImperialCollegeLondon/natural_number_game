import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level1 -- hide
namespace mynat -- hide

/- 
# Addition world

Don't forget to use the drop down boxes on the left to see your tactics and
what you have proved so far.

## Level 2: `add_assoc` -- associativity of addition.

It's well-known that (1 + 2) + 3 = 1 + (2 + 3) -- if we have three numbers
to add up, it doesn't matter which of the additions we do first. This fact
is called *associativity of addition* by mathematicians, and it is *not*
obvious. For example, subtraction really is not associative: $(6 - 2) - 1$
is really not equal to $6 - (2 - 1)$. We are going to have to prove
that addition, as defined the way we've defined it, is associative. 
 
See if you can prove associativity of addition. Hint: because addition was defined
by recursion on the right-most variable, use induction on the right-most
variable (try other variables at your peril!). Note that when Lean writes `a + b + c`,
it means `(a + b) + c`. If it wants to talk about `a + (b + c)` it will put the brackets
in explictly.

Reminder: you are done when you see "Proof complete!" in the top right, and an empty
box (no errors) in the bottom right.
-/

/- Lemma
On the set of natural numbers, addition is associative.
In other words, for all natural numbers $a, b$ and $c$, we have
$$ (a + b) + c = a + (b + c). $$
-/
lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin [nat_num_game]
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

