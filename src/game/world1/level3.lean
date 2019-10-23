import mynat.definition -- hide
namespace mynat -- hide

/-
# World 1 : Tutorial world

## level 3: The rewrite (`rw`) tactic.

The rewrite tactic is the way to "substitute in" the value
of a variable. In general, If you have a hypothesis of the form `A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`.
Below is a theorem which looks obvious, but which cannot be
proved using `refl` and `exact` alone -- you need a rewrite.

Delete the sorry and take a look in the top right box at what we have.
The variables `x`, `y` and `z`
are natural numbers, and we have functions `f` and `g` from natural numbers
to natural numbers. We have a proof `h` of `y = f(x)` and our goal
is to prove that `g(y) = g(f(x))`. This goal is obvious -- we just
substitute in `y = f(x)` into the goal and we're done. In Lean, we do
this substitution using the `rw` tactic. So start your proof with 

`rw h,`

and then hit enter. **don't forget the comma.**
Did you see what happened to the goal? The goal doesn't close,
but it *changes* from `⊢ g y = g (f x)` to `⊢ g (f x) = g (f x)`
(note that computer scientists are a bit less liberal with brackets
than mathematicians!). We can just close this goal with

`refl,`

written on the line after `rw h,`. Don't forget the comma, hit
enter, and enjoy seeing the "Proof complete!" message in the
top right window. The other reason you'll know you're
done is that the bottom right window (the error window)
becomes empty. 

-/

/- Lemma : no-side-bar
For all natural numbers $x$, $y$ and $z$ and all functions $f$
and $g$ from the naturals to themselves, if $y = f(x)$
and then $g(y) = g(f(x))$.
-/
lemma example3 (x y z : mynat) (f g : mynat → mynat)
  (h : y = f(x)) : g(y) = g(f(x)) :=
begin [less_leaky]
  rw h,
  refl

end

/- Tactic : rw
The `rw` tactic is a way to do "substituting in".
If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
and your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s. If you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l`).

### Example:
If it looks like this in the top right hand box:
```
x y : mynat
h : x = y + 3
⊢ 1 + x = y + 4
```

then

`rw h,`

will change the goal into `⊢ 1 + (y + 3) = y + 4`.
Note of course that this goal is still far from solved.

-/

/-

## Exploring your proof.

1) Click on `refl,` and then use the arrow keys to move
your cursor around the proof. Go up and down and note that
the goal changes -- indeed you can inspect Lean's "state" at each
line of the proof (the hypotheses, and the goal).
Try to figure out the exact place where the goal changes.
The comma tells Lean "I've finished writing this tactic now,
please process it." Lean ignores newlines, but pays great
attention to commas.

-/

end mynat -- hide