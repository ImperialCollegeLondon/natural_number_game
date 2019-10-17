import mynat.definition -- hide
namespace mynat -- hide

/-
## Tutorial level 3: The rewrite (`rw`) tactic.

If you have a hypothesis of the form `A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`.
Below is a theorem which looks obvious, but which cannot be
proved using `refl` and `exact` alone -- you need a rewrite.
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
Click on the button, and delete the sorry. Our goal `⊢ x = z` mentions
a variable `x`. Our hypothesis `h1` says that `x = y`. Try the tactic
`rw h1,` (**don't forget the comma**), and see what happens to the goal.
The goal doesn't close, but it changes. Move your cursor around a bit
and get a feeling for the exact place where the goal changes (hint: it's
near the all-important comma).

The `rw h1` tactic changes the `x` in the goal to a `y`. Our goal
has now become `⊢ y = z`, so we can prove it with `exact h2,`. Actually,
there is now another way we can prove it as well; with your goal at `⊢ y = z`,
what happens if you `rw h2,` instead? The `y` in the goal changes to a `z`
and you can now close the goal with `refl,`. There's more than one way
to prove a theorem.

In the next example we will see Peano's axioms, and use the `rw` tactic
on some more complicated goals.
-/

end mynat -- hide