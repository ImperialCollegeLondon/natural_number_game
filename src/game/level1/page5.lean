import mynat.definition -- hide
import mynat.add -- definition of addition
namespace mynat -- hide

/-
## Tutorial page 5: addition

We have a new import -- the definition of addition.

Peano defined addition `a + b` by induction on `b`, or,
more preisely, by *recursion* on `b`. The base case is this:

* `add_zero : ∀ a : mynat, a + 0 = a`

We will call this theorem `add_zero`. **Remember the name of this theorem**.
Mathematicians might call it "Lemma 2.1" or "Hypothesis P6" or something. But
computer scientists call it `add_zero` because it tells you
what the answer to "a add zero" is. If you ever see `x + 0` in your
goal, `rw add_zero` should simplify it to `x`.

The inductive step is this:

* `add_succ : ∀ a d : mynat, a + succ(d) = succ (a + d)`

What's going on here is that we assume `a + d` is already
defined, and we define `a + succ(d)` to be the number after it.
Remember the name of this theorem too -- `add_succ` tells you
how to add a successor to something. If you ever see `... + succ ...`
in your goal, you should be able to use the `rw` tactic to make
progress. Here is a simple example.
-/

/- Theorem
For all natural numbers `a`, we have `a + succ(0) = succ(a)`.
-/
theorem example4 (a : mynat) : a + succ(0) = succ(a) :=
begin [less_leaky]
  rw add_succ,
  rw add_zero,
  refl,
end

/-
First apply `rw add_succ,` and watch the goal change. Don't
forget commas, Now rewrite `add_zero`. Now close the goal with `refl,`.
Move your cursor around until you're happy with what happens when.
When you're happy, let's step into level 2, addition world, and
learn about proof by induction.
-/
end mynat