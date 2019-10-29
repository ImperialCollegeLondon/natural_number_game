import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level5 -- hide
namespace mynat -- hide

/-

# World 2 -- Addition World

## Level 6 -- `add_right_comm`

You have (amongst other things these:

  * `add_assoc : ∀ a b c : mynat, (a + b) + c = a + (b + c)`
  * `add_comm : ∀ a b : mynat, a + b = b + a`

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

1) Press on in addition world, proving things like (a + b = a + c → b = c),
which won't help for multiplication world and for which you will have
to learn several new tactics (there are ten bonus levels, levels 7 to 16), or

2) Leave the world now by clicking "next world". This will take you to world 3,
multiplication world. You won't need to know any new tactics to prove
the big theorem `a * b = b * a`.
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
There is now a fork in the path. Will you click "next level" and learn
some new tactics to deal with harder addition problems, or will you click
on "next world" to battle multiplication with the tactics you have?
You can of course just go to any level or world you like -- we left
them all unlocked.
-/

end mynat -- hide
