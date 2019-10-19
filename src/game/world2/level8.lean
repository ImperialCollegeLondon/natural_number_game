import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level7 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 8 -- `add_right_comm`

You have these:

  * zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)
  * succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b
  * add_zero : ∀ a : mynat, a + 0 = a
  * add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)
  * zero_add : ∀ a : mynat, 0 + a = a`
  * add_assoc : ∀ a b c : mynat, (a + b) + c = a + (b + c)
  * succ_add : ∀ a b : mynat, succ a + b = succ (a + b)
  * add_comm : ∀ a b : mynat, a + b = b + a

Lean sometimes writes `a + b + c`. What does it mean? The convention is
that if there are no brackets displayed in an addition formula, the brackets
are around the left most `+` (Lean's addition is "left associative"). 
So the goal in this one says `(a + b) + c = (a + c) + b. 

If you hadn't picked up on this already, `rw add_assoc` will
change `(x + y) + z` to `x + (y + z)`, but to change it back
you will need `rw ←add_assoc`. Get the left arrow with \l .

Also, you can be (and will need to be, in this level) more precise
about where to rewrite theorems. `rw add_commm,` will just find the
first + it sees and swap it around. You can target more specific
additions like this: `rw add_comm a` will swap around the first
addition of the form `a + ?`, and `rw add_comm a b,` will only
swap additions of the form `a + b`.
-/


/- Lemma
For all natural numebrs $a, b$ and $c$, we have
$$ a + b + c = a + c + b. $$
-/
lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin [less_leaky]
  rw add_assoc,
  rw add_comm b c,
  rw ←add_assoc,
  refl,
end

end mynat -- hide
