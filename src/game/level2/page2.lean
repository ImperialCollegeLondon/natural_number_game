import mynat.definition -- Imports the natural numbers.
import mynat.add -- definition of addition
namespace mynat

/-
Instructions: First carefully explain definition of nat and add. Then
guide them through the first level. 

"We're going to prove this by induction on n, which is a natural
thing to do because we defined addition by recursion on n (you
prove things by induction and define them by recursion).

For the base case, we are going to use the axiom that a + 0 = 0.
refl closes a goal of the form x = x. how to use add_succ here?

etc."
-/

/- Lemma
For all natual numbers $n$, we have $0 + n = n$.
-/
lemma zero_add (n : mynat) : 0 + n = n :=
begin [less_leaky]
  induction n with d hd,
  {
    rw add_zero,
    refl,
  },
  { rw add_succ,
    rw hd,
    refl
  }
end

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

-- first point: needs add_assoc, zero_add, add_zero
def collectible_01 : add_monoid mynat := by structure_helper
--#print axioms collectible_01 -- prove you got this by uncommenting

end mynat -- hide 