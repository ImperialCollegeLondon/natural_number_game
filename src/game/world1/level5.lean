import mynat.definition -- hide
import mynat.add -- definition of addition
namespace mynat -- hide

/-
# World 1 : Tutorial world

## Level 5: addition

We have a new import -- the definition of addition.

Peano defined addition `a + b` by induction on `b`, or,
more precisely, by *recursion* on `b`. He first explained how to add 0 to a number:
this is the base case.

* `add_zero : ∀ a : mynat, a + 0 = a`

We will call this theorem `add_zero`. **Note the name of this theorem**.
Mathematicians sometimes call it "Lemma 2.1" or "Hypothesis P6" or something. But
computer scientists call it `add_zero` because it tells you
what the answer to "a add zero" is. It's a *much* better name than "Lemma 2.1".
Even better, we can use the rewrite tactic with `add_zero`.
If you ever see `x + 0` in your goal, `rw add_zero,` should simplify it to `x`.

Now here's the inductive step. If you know how to add `d` to `a`, then
Peano tells you how to add `succ(d)` to `a`. It looks like this:

* `add_succ : ∀ a d : mynat, a + succ(d) = succ (a + d)`

What's going on here is that we assume `a + d` is already
defined, and we define `a + succ(d)` to be the number after it.
**Note the name of this theorem too** -- `add_succ` tells you
how to add a successor to something. If you ever see `... + succ ...`
in your goal, you should be able to use `rw add_succ,` to make
progress. Here is a simple example where we shall see both.

Delete `sorry`. Observe that the goal mentions `... + succ ...`. So type

`rw add_succ,`

and hit enter; see the goal change. **Don't forget the commma**.
Do you see that the goal now mentions ` ... + 0 ...`? So type

`rw add_zero,`

and then observe that you can close the goal with

`refl,`

and you're done. You might want to review this proof now; at
three lines long it is our current record. Click on a line in the proof
and then use the arrow keys to move your cursor
around (try going up and down first), and you can see what
Lean is thinking on each line of the proof. The goal changes
just before each comma. That's why commas are important.

FAQ. Question: why has the top left hand box gone blank?
Answer: Maybe you tried a tactic which didn't work. Or maybe you're
in the middle of typing a tactic. Try deleting up to the last
comma, or adding a new comma. Look at the
error message. What line is the first error on? Perhaps
Lean thinks you're in the middle of writing a tactic that you
think you finished. Did you perhaps forget a comma somewhere?

When you're happy, let's move onto world 2, addition world, and
learn about proof by induction. Click on "next world" in the top right.
-/

/- Lemma : no-side-bar
For all natural numbers `a`, we have `a + succ(0) = succ(a)`.
-/
lemma add_succ_zero (a : mynat) : a + succ(0) = succ(a) :=
begin [less_leaky]
  rw add_succ,
  rw add_zero,
  refl,




  
end

end mynat