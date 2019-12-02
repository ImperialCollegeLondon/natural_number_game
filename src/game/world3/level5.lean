import game.world3.level4 -- hide
import mynat.mul -- hide

namespace mynat -- hide

/-
# Multiplication World

## Level 5: `mul_assoc`

We now have enough to prove that multiplication is associative.

## Random tactic hints

1) Did you know you can do `repeat {rw mul_succ}`?

2) Did you know you can do `rwa [hd, mul_add]`?
I learnt that trick from Ken Lee. Ken spotted that
`rwa` will do the rewrites and will then check to
see if the goal can be proved by `refl`, and if it
can, it will close it! [It will also close goals which
are exactly equal to hypotheses, which will be helpful later on.]
-/

/- Lemma
Multiplication is associative.
In other words, for all natural numbers $a$, $b$ and $c$, we have
$$ (ab)c = a(bc). $$
-/
lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin [nat_num_game]
  induction c with d hd,
  { 
    repeat {rw mul_zero},
  },
  {
    rw mul_succ,
    rw mul_succ,
    rw hd,
    rw mul_add,
    refl,


  }
end

/-
A mathematician could now remark that you have proved that the natural
numbers form a monoid under multiplication.
-/
def collectible_4 : monoid mynat := by structure_helper -- hide

end mynat -- hide
