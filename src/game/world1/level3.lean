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
are natural numbers. We have a proof `h1` of `x = y` and a proof
`h2` of `y = z`. Our goal is to prove that `x = z`. We're going
to give a two-line proof of this goal. Start with 

`rw h1,`

and then hit enter. **don't forget the comma.**
Did you see what happened to the goal? The goal doesn't close,
but it *changes* from `⊢ x = z` to `⊢ y = z`. We used the proof
`h1` of `x = y` to replace an `x` by a `y`.

After `rw h1,` our goal
has now become `⊢ y = z`, which is exactly hypothesis `h2`,
so we can prove this new goal by writing

`exact h2,`

on the line after `rw h1,`. Don't forget the comma, hit
enter, and enjoy seeing the "Proof complete!" message in the
top right window. The other reason you'll know you're
done is that the bottom right window (the error window)
becomes empty. 

Before you click "next level" and start to learn about
Peano's axioms, you might want to read
the comments underneath the proof, as there are a couple
of extra things you might want to try.
-/

/- Lemma : no-side-bar
For all natural numbers $x$, $y$ and $z$, if $x = y$
and $y = z$ then $x = z$.
-/
lemma example3 (x y z : mynat) (h1 : x = y) (h2 : y = z) : x = z :=
begin [less_leaky]
  rw h1,
  exact h2




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

## Extras

1) Click on `exact h2,` and then use the arrow keys to move
your cursor around the proof. Go up and down and note that
the goal changes -- indeed you can inspect Lean's "state" at each
line of the proof (the hypotheses, and the goal).
Try to figure out the exact place where the goal changes.
The comma tells Lean "I've finished writing this tactic now,
please process it." Lean ignores newlines, but pays great
attention to commas.

2) Can you find a different proof of this theorem which uses
two rewrites and `refl`? The answer is below.

After `rw h1,`, when your goal is `⊢ y = z`, what happens if you try `rw h2,` instead
of `exact h2`? 
The `y` in the goal changes to a `z` and you can now close the goal with `refl,`.
Try it to check. There's more than one way to prove a theorem. 

In fact here's a third way -- delete your proof
completely and try starting with `rw ← h2,`. Don't forget etc etc. You get the left arrow by typing `\l`.
Can you figure out what happened? Here's what's going on. 
What does the tactic `rw h1,` do to the goal? It replaces occurrences of the left hand
side of hypothesis `h1` with the right hand side. The ← switches this behaviour -- it makes Lean replace
occurrences of the right hand side of the hypothesis with the left hand side. There are at least three ways
to proceed to solve the goal from here -- you might want to try and find them. 

Remember that you can review the `rw` tactic by looking in the tactic drop-down box on the left.
-/

end mynat -- hide