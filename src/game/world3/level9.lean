import game.world3.level8 -- hide
import mynat.mul -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 9: `mul_left_comm`

You are equipped with

* `mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c)`
* `mul_comm (a b : mynat) : a * b = b * a`

Re-read the docs for `rw` so you know all the tricks.
You can see them in the "tactics" drop-down menu on the left.
-/

/- Lemma
For all natural numbers $a$ $b$ and $c$, we have
$$a(bc)=b(ac)$$
-/
lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin [nat_num_game]
  rw ←mul_assoc,
  rw mul_comm a, 
  rw mul_assoc,
  refl,



end

/-
And now I whisper a magic incantation
-/
attribute [simp] mul_assoc mul_comm mul_left_comm
/-
and all of a sudden Lean can automatically do levels which are
very boring for a human, for example
-/
example (a b c d e : mynat) :
(((a*b)*c)*d)*e=(c*((b*e)*a))*d :=
begin
  simp,
end 

/-
If you feel like attempting Advanced Multiplication world
you'll have to do Function World and the Proposition Worlds first.
These worlds assume a certain amount of mathematical maturity
(perhaps 1st year undergraduate level). 
Your other possibility is Power World, with the "final boss".
-/

end mynat -- hide
