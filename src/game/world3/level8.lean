import game.world3.level7 -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 8: `mul_comm`

Finally, the boss level of multiplication world. But (assuming you
didn't cheat) you are well-prepared for it -- you have `zero_mul`
and `mul_zero`, as well as `succ_mul` and `mul_succ`. After this
level you can of course throw away one of each pair if you like,
but I would recommend you hold on to them, sometimes it's convenient
to have exactly the right tools to do a job.
-/

/- Lemma
Multiplication is commutative.
-/
lemma mul_comm (a b : mynat) : a * b = b * a :=
begin [less_leaky]
  induction b with d hd,
  { 
    rw zero_mul,
    rw mul_zero,
    refl,
  },
  {
    rw succ_mul,
    rw ←hd,
    rw mul_succ,
    refl,
  }
end

/-
You've now proved that the natural numbers are a commutative semiring!
That's the last collectible in Multiplication World. 

Todo -- add `mul_left_comm` after this because then `simp` will be able to prove
`a*(b*c)=c*(b*a)` and more.

There used to be some very poorly-explained advanced multiplication levels
here, but they have been removed for a few days while I take a look at
where people are stuck and decide how best to teach them.

Until then, you can move
straight on to Power World by selecting "Next World" in the top right
and go and get that big collectible at the end of it,

-/
def collectible_06 : comm_semiring mynat := by structure_helper -- hide

-- begin hide
lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
  rwa [←mul_assoc, mul_comm a, mul_assoc],
end

attribute [simp] mul_assoc mul_comm mul_left_comm
example (a b c d e : mynat) :
(((a*b)*c)*d)*e=(c*((b*e)*a))*d := begin
  simp,
end 
-- end hide

end mynat -- hide
