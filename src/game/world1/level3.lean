import mynat.definition -- hide
namespace mynat -- hide

/-
## Tutorial world, level 3: The rewrite (`rw`) tactic.

If you have a hypothesis of the form `A = B`, and your
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

Move your cursor around a bit
and get try and find the exact place where the goal changes.
The comma indicates that we are finished with our tactic, so
the goal changes just before the comma. Without the comma
the system expects us to write more. If the top left window
ever goes blank, it might well be because you forgot a comma.

After `rw h1,` our goal
has now become `⊢ y = z`, which is exactly hypothesis `h2`,
so we can prove this new goal by writing

`exact h2,`

on the line after `rw h1`. Don't forget the comma, hit
enter, and enjoy seeing the "no goals" message in the
top left window. Before you click "next level" -- can you find a different
proof of this theorem which uses `refl`? The answer is below the lemma.
-/

/- Lemma
For all natural numbers $x$, $y$ and $z$, if $x = y$
and $y = z$ then $x = z$.
-/
lemma example3 (x y z : mynat) (h1 : x = y) (h2 : y = z) : x = z :=
begin [less_leaky]
  rw h1,
  exact h2





end

/-

There is another way we can prove this goal;
after `rw h1,`, when your goal is `⊢ y = z`, what happens if you try `rw h2,` instead?
The `y` in the goal changes to a `z` and you can now close the goal with `refl,`.
Try it to check. There's more than one way to prove a theorem.

In the next example we will see Peano's axioms, and use the `rw` tactic
on a more complicated goal.
-/

end mynat -- hide