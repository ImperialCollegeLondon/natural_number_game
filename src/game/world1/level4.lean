import mynat.add -- definition of addition
namespace mynat -- hide

/- Axiom : add_zero (a : mynat) :
a + 0 = a
-/

/- Axiom : add_succ (a b : mynat) :
a + succ(b) = succ(a + b)
-/

/-
# Tutorial world

## Level 4: addition

We have a new import -- the definition of addition.

Peano defined addition `a + b` by induction on `b`, or,
more precisely, by *recursion* on `b`. He first explained how to add 0 to a number:
this is the base case.

* `add_zero (a : mynat) : a + 0 = a`

We will call this theorem `add_zero`. More precisely, `add_zero` is the name
of the *proof* of the theorem. **Note the name of this proof**.
Mathematicians sometimes call it "Lemma 2.1" or "Hypothesis P6" or something. But
computer scientists call it `add_zero` because it tells you
what the answer to "$x$ add zero" is. It's a *much* better name than "Lemma 2.1".
Even better, we can use the rewrite tactic with `add_zero`.
If you ever see `x + 0` in your goal, `rw add_zero` should simplify it to `x`.
This is because `add_zero` is a proof that `x + 0 = x` (more precisely,
`add_zero x` is a proof that `x + 0 = x` but Lean can figure out the `x` from the context).

Now here's the inductive step. If you know how to add `d` to `a`, then
Peano tells you how to add `succ(d)` to `a`. It looks like this:

* `add_succ (a d : mynat) : a + succ(d) = succ (a + d)`

What's going on here is that we assume `a + d` is already
defined, and we define `a + succ(d)` to be the number after it.
**Note the name of this proof too** -- `add_succ` tells you
how to add a successor to something. If you ever see `... + succ ...`
in your goal, you should be able to use `rw add_succ,` to make
progress. Here is a simple example where we shall see both. Let's prove
that $x$ add the number after $0$ is the number after $x$.

Delete `sorry` (don't forget you can widen this box if you can't see the sorry).
Observe that the goal mentions `... + succ ...`. So type

`rw add_succ,`

and hit enter; see the goal change. **Don't forget the commma**.
Do you see that the goal now mentions ` ... + 0 ...`? So type

`rw add_zero,`

and then observe that you can close the goal with

`refl,`

and you're done. You have finished tutorial world!

## Examining proofs.

You might want to review this proof now; at
three lines long it is our current record. Click on a line in the proof
and use the L/R arrow keys to put your cursor as far left as it will go.
Then use the U/D arrow keys to move your cursor
up and down from line to line, and you can see what
Lean is thinking on each line of the proof.

## No problems?

When you're happy, let's move onto Addition World, and
learn about proof by induction. Go back to the main menu and select addition world.

## Problems? 

See below the lemma.
-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma add_succ_zero (a : mynat) : a + succ(0) = succ(a) :=
begin [less_leaky]
  rw add_succ,
  rw add_zero,
  refl,




  
end

end mynat -- hide

/-
## Problems?

Question: why has the top right hand box gone blank?

Answer: Maybe you tried a tactic which didn't work. Or maybe you're
in the middle of typing a tactic. Try deleting up to the last
comma, *or adding a comma at the end of your code*. Look at the
error message. What line is the first error on? Perhaps
Lean thinks you're in the middle of writing a tactic command that you
think you finished. If Lean is still attempting to process a tactic
command it won't display anything. You can get it to stop processing by
adding a comma. 

If the worst comes to the worst, just delete what you wrote. Most people
with problems have written random stuff in the proof box. The only thing
you're supposed to be writing is lines like

`rw add_zero,`
`rw h,`
`refl,`

One line of code with a comma at the end. Nothing else at all goes in the box.

If you cannot see what you have done wrong, you can always
<a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/SOLUTIONS.md"
  target="blank">take a look at the solutions</a> (github.com, opens in new window).
-/