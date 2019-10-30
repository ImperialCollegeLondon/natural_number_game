import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level5 -- hide
import tactic.ring -- hide
namespace mynat -- hide



/-

# World 2 -- Addition World

## Level 6 -- `add_right_comm`

You have (amongst other things these:

  * `add_assoc (a b c : mynat) : (a + b) + c = a + (b + c)`
  * `add_comm (a b : mynat) : a + b = b + a`

Lean sometimes writes `a + b + c`. What does it mean? The convention is
that if there are no brackets displayed in an addition formula, the brackets
are around the left most `+` (Lean's addition is "left associative"). 
So the goal in this level is `(a + b) + c = (a + c) + b`. This isn't
quite `add_assoc` or `add_comm`, it's something you'll have to prove
by putting these two theorems together.

If you hadn't picked up on this already, `rw add_assoc` will
change `(x + y) + z` to `x + (y + z)`, but to change it back
you will need `rw ← add_assoc`. Get the left arrow with \l .
Similarly, if `h : a = b` then `rw h` will change `a`'s to `b`'s
and `rw ← h` will change `b`'s to `a`'s.

Also, you can be (and will need to be, in this level) more precise
about where to rewrite theorems. `rw add_comm,` will just find the
first `? + ?` it sees and swap it around. You can target more specific
additions like this: `rw add_comm a` will swap around
additions of the form `a + ?`, and `rw add_comm a b,` will only
swap additions of the form `a + b`.

After you have solved this level, you have a choice of two things.

1) Press on in addition world (there are ten more levels),
proving things like (a + b = a + c → b = c).
You have never proved a goal like that before; your current tactics
can't prove implications and you need to learn some new ones, specifically
adapted to work with hypotheses and goals of the form `P → Q`;

2) Solve this level and then leave addition world completely by clicking "next world".
This will take you to world 3, multiplication world.
You won't need to know any new tactics to prove
the big theorem `a * b = b * a` and get the `comm_semiring` collectible.
-/

/- Lemma
For all natural numbers $a, b$ and $c$, we have
$$ a + b + c = a + c + b. $$
-/
lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin [less_leaky]
  rw add_assoc,
  rw add_comm b c,
  rw ←add_assoc,
  refl,
end

/-
If you have got this far, then you have become very good at
manipulating equalities in Lean. You have also collected
four collectibles:

```
mynat.add_semigroup -- (after world 2-2)
mynat.add_monoid -- (after world 2-2)
mynat.add_comm_semigroup mynat (after world 2-4)
mynat.add_comm_monoid -- (after world 2-4)
```

There is now a fork in the path. In V1.1 of this game you will
be able to choose between one of two new worlds at this point.
But until we get there, it's either "next level" or "next world",
and I just broke "next level" -- TODO -- fix it?

Will you click "next level" and learn some new tactics (`have` and `intro`,
and more, still not documented particularly well in v1.01)
to deal with addition problems involving implications
(NB this is greyed out in v1.01),
or will you stick to the tactics you know
and click on "next world" to move on to Multiplication World and
collect such advanced collectibles as `mynat.semiring` and
`mynat.distrib`, and the famous collectible at the end of world 4?

While you are deciding, didn't you think that solving this level
was boring? check out this AI called `simp`:

First we have to get the collectible, which we do by saying
the magic words which make Lean's type class inference
system give it to us.
-/
instance : add_comm_monoid mynat := by structure_helper

/-
Now the `simp` AI becomes accessible (it's just an advanced
tactic really), and can nail some really tedious-for-a-human-to-solve
goals. 
-/

example (a b c d e : mynat) :
(((a+b)+c)+d)+e=(c+((b+e)+a))+d := begin
  simp
end 

/-
Imagine having to do that one by hand! The AI closes the goal
because it knows how to use associativity and commutativity
sensibly in a commutative monoid.
-/
end mynat -- hide
