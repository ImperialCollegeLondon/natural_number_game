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

There are now two paths you can take. You can play it safe and move
straight on to Power World by selecting "Next World" in the top right
and go and get that big collectible at the end of it,
or you can push further into uncharted
(i.e. currently poorly documented) territory and see if you can solve
some harder levels in multiplication world, by selecting "Next Level".
Note that in the next version of the game these levels will split off
into a different Advanced Multiplication World and the tactics you
need to solve them will actually be explained to you properly. Until then,
you might just have to look at the 
<a href="http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html" target="blank">tactic guide</a>.
Note that level 13 is currently in the wrong place and you could do that
one easily. But the others need tactics like `intro` which you might
not know yet.

-/
def collectible_06 : comm_semiring mynat := by structure_helper -- hide

end mynat -- hide
