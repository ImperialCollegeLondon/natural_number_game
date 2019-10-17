import mynat.definition
import mynat.add
import game.level1.page2
namespace mynat


/-
Proving add_comm immediately is still tricky;
trying it reveals a natural intermediate lemma which we prove first.
-/

/- Lemma
For all natural numbers $a, b$, we have
$$ \operatorname{succ}(a) + b = \operatorname{succ}(a + b). $$
-/
lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin [less_leaky]
  induction b with d hd,
  {
    refl
  }, 
  { rw add_succ,
    rw hd,
    rw add_succ,
    refl
  }
end

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

-- level up
def collectible_02 : add_comm_monoid mynat := by structure_helper
--#print axioms collectible_02

end mynat