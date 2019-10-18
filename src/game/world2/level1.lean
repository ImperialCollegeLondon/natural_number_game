import mynat.definition -- Imports the natural numbers.
import mynat.add -- imports addition.
namespace mynat -- hide

/- 
## Level 2 -- addition world

Welcome to level 2. Let me remind you the tools we're equipped with.

## Data:

  * a type called `mynat`
  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after n".
  * Usual numerical notation 0,1,2,3,4,5 etc.
  * Addition (with notation a + b).

## Theorems:

  * `zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)`, the statement that zero isn't a successor.
  -- this ensures that there is more than one natural number. Use with `rw`.
  * `succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b`, the statement that
     if succ(a) = succ(b) then a = b. Use with `rw`.
  * The principle of mathematical induction. Use with `induction` (see below)
  * `add_zero : ∀ a : mynat, a + 0 = a`
  * `add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)`

## Tactics:

  * `refl` -- proves goals of the form `X = X`
  * `exact h` -- proves a goal if it is exactly equal to a hypothesis h 
  * `rw h` -- if h is a proof of `A = B`, changes all A's in the goal to B's.
  * `induction n with d hd` -- you're about to see this in action.

Now let's see induction in action. We're going to prove

  `zero_add : ∀ n : mynat, 0 + n = n`. 

Wait -- what is going on here? Didn't we already prove that adding zero to n gave us n?
No we didn't! We proved n + 0 = n -- that was called `add_zero`. We're now
trying to prove `zero_add`, which says `0 + n = n`. But aren't these two theorems
the same? No they're not! It is *true* that `x + y = y + x`, but we haven't
*proved* it yet, and in fact we will need both `add_zero` and `zero_add` in order
to prove this. In fact `x + y = y + x` is the boss page (note: when we change "page"
  to "level" it will be the boss level) for addition world. `add_zero` is one
  of Peano's axioms. To prove `zero_add` we need to use induction. While we're here,
  note that `zero_add` is about zero add something, and `add_zero` is about something add zero.
  The names tell you what the theorem is. Anyway, let's prove it.
-/

/- Lemma
For all natual numbers $n$, we have $0 + n = n$.
-/
lemma zero_add (n : mynat) : 0 + n = n :=
begin [less_leaky]
  induction n with d hd,
  {
    rw add_zero,
    refl,
  },
  { rw add_succ,
    rw hd,
    refl
  }
end

/-
Click on the button, delete `sorry` and replace it with `induction n with d hd,`
and **don't forget the comma**. Hit enter, wait for Lean to finish thinking,
and let's see what we have.

When Lean has finished thinking, we see that we now have two goals! The
induction tactic has generated for us a base case with n=0 and an inductive
step. Let's first talk about the base case. 

The base case is `0 + 0 = 0`. Let's solve this goal first.
Remember that `add_zero` (the theorem we have already) says that `x + 0 = x`
(for any x) so we can try `rw add_zero,`. What do you think the goal will
change to? You should be able to solve this one yourself.

We now only have one goal left -- the inductive step. As you can see on the right,
we have a natural number `d`, and the inductive hypothesis `hd : 0 + d = d`. 
Our goal is to prove `0 + succ d = succ d`. In words, we're showing that
if the theorem is true for `d`, then it's true for the number after `d`. Once
we've done this, we will have proved `zero_add` by the principle of mathematical induction.

To prove our goal, we need to use `add_succ`. We know that `add_succ 0 d`
is the result that 0 + succ d = succ (0 + d), so the first thing
we need to do is to replace the left hand side `0 + succ d` of our
goal with the right hand side. We do this with the `rw` command. You can write

`rw add_succ 0 d,`

but just `rw add_succ,` will work fine, Lean will guess the variables if you don't
tell it them. Don't forget the comma though. The goal should change to

`⊢ succ (0 + d) = succ d`

Now remember our inductive hypothesis `hd : 0 + d = d`. We need
to rewrite this too! Type 

`rw hd,`

(don't forget the comma). The goal will now change to

`⊢ succ d = succ d`

This goal can be solved with the `refl` tactic. After you apply it,
Lean will inform you that there are no goals left. You are done!

Those four tactics -- 

* `induction`, 
* `rw`, 
* `exact`, and
* `refl`

will get you quite a long way through this game. You should be able to do all of
addition world (although you'll need more tactics to do the bonus levels) and
also all of multiplication world. If you're interested in seeing more tactics,
or other ways of applying these tactics, take a look at the [tactic guide]
(http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html)!

One last thing (which you can learn from the tactic guide) -- `rw h` replaces the left
hand side of h in the goal with the right hand side.
If you want to replace the right hand side with the left hand side, try `rw ←h` (you can get
the left arrow by typing \l).

If you get stuck or want to know more, ask in `#new members` at
<https://leanprover.zulipchat.com> (real name preferred)

Good luck! 

-/

end mynat -- hide