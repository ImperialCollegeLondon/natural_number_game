import mynat.mul -- hide
namespace mynat -- hide

/-
# Tutorial world

## level 2: The rewrite (`rw`) tactic.

The rewrite tactic is the way to "substitute in" the value
of a variable. In general, if you have a hypothesis of the form `A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`.
Below is a theorem which cannot be
proved using `refl` -- you need a rewrite first.

Delete the sorry and take a look in the top right box at what we have.
The variables $x$ and $y$ are natural numbers, and we have
a proof `h` that $y = x + 7$. Our goal
is to prove that $2y=2(x+7)$. This goal is obvious -- we just
substitute in $y = x+7$ and we're done. In Lean, we do
this substitution using the `rw` tactic. So start your proof with 

`rw h,`

and then hit enter. **Don't forget the comma.**
Did you see what happened to the goal? The goal doesn't close,
but it *changes* from `⊢ 2 * y = 2 * (x + 7)` to `⊢ 2 * (x + 7) = 2 * (x + 7)`.
We can just close this goal with

`refl,`

by writing it on the line after `rw h,`. Don't forget the comma, hit
enter, and enjoy seeing the "Proof complete!" message in the
top right window. The other reason you'll know you're
done is that the bottom right window (the error window)
becomes empty. When you've finished reading the comments below
the proof, click "Next Level" in the top right to proceed to the next
level in this world.

-/

/- Lemma : no-side-bar
If $x$ and $y$ are natural numbers, 
and $y=x+7$, then $2y=2(x+7)$. 
-/
lemma example2 (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
begin [nat_num_game]
  rw h,
  refl
  

end

/- Tactic : rw

## Summary

If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. Variants: `rw ← h` (changes
`Y` to `X`) and
`rw h at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).

## Details

The `rw` tactic is a way to do "substituting in". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s. 

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).
For example, in world 1 level 4
we learn about `add_zero x : x + 0 = x`, and `rw add_zero`
will change `x + 0` into `x` in your goal (or fail with
an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l` and
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
x y : mynat
h : x = y + y
⊢ succ (x + 0) = succ (y + y)
```

then

`rw add_zero,`

will change the goal into `⊢ succ x = succ (y + y)`, and then

`rw h,`

will change the goal into `⊢ succ (y + y) = succ (y + y)`, which
can be solved with `refl,`.

### Example: 
You can use `rw` to change a hypothesis as well. 
For example, if your local context looks like this:
```
x y : mynat
h1 : x = y + 3
h2 : 2 * y = x
⊢ y = 3
```
then `rw h1 at h2` will turn `h2` into `h2 : 2 * y = y + 3`.
-/

/-

## Exploring your proof.

Click on `refl,` and then use the arrow keys to move
your cursor around the proof. Go up and down and note that
the goal changes -- indeed you can inspect Lean's "state" at each
line of the proof (the hypotheses, and the goal).
Try to figure out the exact place where the goal changes.
The comma tells Lean "I've finished writing this tactic now,
please process it." Lean ignores newlines, but pays great
attention to commas.

## The tactic index

The documentation for `rw` just appeared in the list of tactics
in the box on the left. Play around with the menus on the left
and see what is there currently. More information will appear as you progress.

## Bewildered?

Doesn't work? Weird error that won't go away? You can check out
the 
<a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/SOLUTIONS.md"
  target="blank">solutions</a> (github.com, opens in new window).
  Solutions to every level are here.
-/

end mynat -- hide