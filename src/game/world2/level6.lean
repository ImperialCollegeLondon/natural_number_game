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

## Where next?

There are ten more levels about addition after this one, but before
you can attempt them you need to learn some more tactics. So after this
level you have a choice -- either move on to world 3 (which you can
solve with the tactics you know) or try world 5 (and learn some new ones).
Use the "next world" and "previous world" buttons to move between worlds.
Note that advanced addition world is not yet available in 1.07beta.

Clicking "next world" once will take you to world 3, multiplication world.
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

In Multiplication World you will be able to collect such
advanced collectibles as `mynat.comm_semiring` and
`mynat.distrib`, and then move on to power world and
the famous collectible at the end of it.

One last thing -- didn't you think that solving this level
`add_right_comm` was boring? check out this AI that can do it for us.

First we have to get the `add_comm_monoid` collectible,
which we do by saying the magic words which make Lean's type class inference
system give it to us.
-/
instance : add_comm_monoid mynat := by structure_helper

/- Tactic : simp
The `simp` tactic does basic automation. By level 2-6 you
have proved enough about addition for `simp` to be able
to solve all equalities whose proofs involve a tedious number
of rewrites of `add_assoc` and `add_comm`, and by
level 3-9 the same is true of `mul_assoc` and `mul_comm`.

### Example:
If our goal is this:
```
⊢ a + b + c + d + e = c + (b + e + a) + d
```

and you are after level 2-6, then you've proved
enough about addition to solve this level with `simp`. 
Note however that you can't prove `add_assoc` with `simp`,
because `add_assoc` is an ingredient to get `simp` working.

### Example:
If our goal is this:
```
⊢ a * b * c = c * b * a
```
then as long as you're after 3-9, `simp` will close this
goal.
-/

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
