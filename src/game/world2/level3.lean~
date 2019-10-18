import mynat.definition -- hide
import mynat.add -- hide
import game.level2.page2 -- hide
namespace mynat -- hide

/- 
## Level 2 -- addition world

## You are equipped with:

  * `zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)`
  * `succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b`
  * `add_zero : ∀ a : mynat, a + 0 = a`
  * `add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)`
  * `zero_add` : ∀ a : mynat, 0 + a = a`
  * `add_assoc : ∀ a b c : mynat, (a + b) + c = a + (b + c)`

Oh no! On the way to `add_comm`, a wild `succ_add` appears. You will
need this theorem to prove `a + b = b + a` so you'd better prove it first.
NB think about why is it called `succ_add` .
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

end mynat -- hide 