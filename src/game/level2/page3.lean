import mynat.definition -- hide
import mynat.add -- hide
import game.level1.page2 -- hide
namespace mynat -- hide


/-
If you try to prove commutativity directly, you will realise that you
are missing an intermediate lemma. So let's prove that lemma first.
It's called `succ_add`.
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

/-
Hopefully now we have enough to prove commutativity, although it
is still a little tricky.
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

end mynat -- hide