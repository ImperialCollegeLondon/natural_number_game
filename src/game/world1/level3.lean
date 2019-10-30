import mynat.definition -- hide
import mynat.mul -- hide
namespace mynat -- hide

/-
# World 1 : Tutorial world

## level 3: The rewrite (`rw`) tactic.

The rewrite tactic is the way to "substitute in" the value
of a variable. In general, If you have a hypothesis of the form `A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`.
Below is a theorem which cannot be
proved using `refl` and `exact` alone -- you need a rewrite.

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
becomes empty. 

-/

/- Lemma : no-side-bar
If $x$ and $y$ are natural numbers, 
and $y=x+7$, then $2y=2(x+7)$. 
-/
lemma example3 (x y z : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
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

### Example: 
You can rewrite a hypothesis as well. 
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

-/

end mynat -- hide