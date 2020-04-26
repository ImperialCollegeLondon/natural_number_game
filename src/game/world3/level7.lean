import game.world3.level6 -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 7: `add_mul`

We proved `mul_add` already, but because we don't have commutativity yet
we also need to prove `add_mul`. We have a bunch of tools now, so this won't
be too hard. You know what -- you can do this one by induction on any of
the variables. Try them all! Which works best? If you can't face
doing all the commutativity and associativity, remember the high-powered
`simp` tactic mentioned at the bottom of Addition World level 6,
which will solve any puzzle which needs only commutativity
and associativity. If your goal looks like `a+(b+c)=c+b+a` or something,
don't mess around doing it explicitly with `add_comm` and `add_assoc`,
just try `simp`.
-/

/- Lemma
Addition is distributive over multiplication.
In other words, for all natural numbers $a$, $b$ and $t$, we have
$$ (a + b) \times t = at + bt. $$
-/
lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin [nat_num_game]
  induction b with d hd,
  { 
    rw zero_mul,
    rw add_zero,
    rw add_zero,
    refl
  },
  {
    rw add_succ,
    rw succ_mul,
    rw hd,
    rw succ_mul,
    rw add_assoc,
    refl
  }
end

/-
A mathematician would now say that you have proved that the natural
numbers are a semiring. This sounds like a respectable result.
-/

def right_distrib := add_mul -- alternative name
instance : semiring mynat := by structure_helper

/-
Lean would add that you have also proved that they are a `distrib`. 
However this concept has no mathematical name at all -- this says something
about the regard with which mathematicians hold this collectible.
This is an artefact of the set-up of collectibles in Lean. You consider politely
declining Lean's offer of a `distrib` collectible.
You are dreaming of the big collectible at the end of power world.
-/

instance : distrib mynat := by structure_helper -- 

end mynat -- hide
