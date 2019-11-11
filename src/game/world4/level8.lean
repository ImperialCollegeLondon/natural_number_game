import game.world4.level7 -- hide
-- incantation for importing ring into framework -- hide
import tactic.ring -- hide
meta def less_leaky.interactive.ring := tactic.interactive.ring -- hide
namespace mynat -- hide
instance : comm_semiring mynat := by structure_helper -- you just levelled up

def two_eq_succ_one : (2 : mynat) = succ 1 := rfl -- hide

/- 
# Power World
-/


/-
## Level 8: `add_squared`

[final boss music] 

You see something written on the stone dungeon wall:
```
begin
  rw two_eq_succ_one,
  rw one_eq_succ_zero,
  repeat {rw pow_succ},
  ...
```

and you can't make out the rest because there's a kind
of thing in the way that will magically disappear
but only when you've beaten the boss.

-/

/- Theorem
For all naturals $a$ and $b$, we have
$$(a+b)^2=a^2+b^2+2ab.$$
-/
lemma add_squared (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b :=
begin [less_leaky]
  rw two_eq_succ_one,
  rw one_eq_succ_zero,
  repeat {rw pow_succ},
  repeat {rw pow_zero},
  ring,






















end

/- 
As the boss lies smouldering, you notice on the dungeon wall that
<a href="https://twitter.com/XenaProject/status/1190453646904958976?s=20/" target="blank">
two more lines of code are now visible under the first three...</a> (Twitter.com)

I just beat this level with 27 rewrites followed by a `refl`. 
Can you do any better? If you beat it then well done. Do you
fancy doing $(a+b)^3$ now? You might want to read 
<a href="https://xenaproject.wordpress.com/2018/06/13/ab3/" target="blank">
this Xena Project blog post</a> before you start though.
-/

/-
If you got this far -- very well done! If you only learnt the three
tactics `rw`, `induction` and `refl` then there are now more tactics to
learn; go back to the main menu and choose Function World. 

The main thing we really want to impress upon people is that we believe
that *all of pure mathematics* can be done in this new way.
A system called Coq (which is very like Lean) has
<a href="https://hal.inria.fr/hal-00816699" target="blank">
checked the proof of the Feit-Thompson theorem</a> (hundreds of pages of
group theory) and Lean has a
<a href="https://leanprover-community.github.io/lean-perfectoid-spaces/"
  target="blank">
definition of perfectoid spaces</a> (a very complex modern
mathematical structure). I believe that these systems will one day
cause a paradigm shift in the way mathematics is done, but first we need
to build what we know, or at least build enough to state what we
mathematicians believe. If you want to get involved, come and join
us at the <a href="https://leanprover.zulipchat.com" target="blank">Zulip Lean chat</a>.
The #new members stream is a great place to start asking questions.
-/

end mynat -- hide
