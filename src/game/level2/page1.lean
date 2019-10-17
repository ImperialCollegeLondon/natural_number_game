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

What is going on here? Didn't we already prove that adding zero to n gave us n?
No we didn't! We proved n + 0 = n -- that was called `add_zero`. We're now
trying to prove `zero_add`, which says `0 + n = n`. But aren't these two theorems
the same? No they're not! It is *true* that `x + y = y + x`, but we haven't
*proved* it yet, and in fact we will need both `add_zero` and `zero_add` in order
to prove this. In fact `x + y = y + x` is the boss page (note: when we change "page"
  to "level" it will be the boss level) for addition world. `add_zero` is one
  of Peano's axioms. To prove `zero_add` we need to use induction.
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
-/



/-
Those four tactics -- `induction`, `rw`, `exact` and `refl` will get you quite a long way
through this game. You'll have trouble with 1.4 but just skip it and go on to 2.1, the
stuff in 1.4 isn't needed for 2.1 onwards anyway. Oh -- one last thing -- `rw h` replaces
the left hand side of h in the goal with the right hand side. If you want to replace
the right hand side with the left hand side, try `rw ←h`. If you get stuck or want
to know more, ask in `#new members` at https://leanprover.zulipchat.com (I'm sorry
I can't make these links live, we're working on it, this is still only a preliminary
version of everything). If you're a first year at Imperial you can on Blackboard in the forum..

Here are some other resources:

List of some basic tactics is here:

http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/tactics/tacticindex.html#basic-tactic-list

Preliminary ideas here:

https://xenaproject.wordpress.com/2017/10/31/building-the-non-negative-integers-from-scratch/

might be of some help. The one big difference between that blog post
and this game is that in this game we make all the definitions for you,
and just leave you with the fun part of proving the theorems.
Why not just try playing though, and if you get stuck then ask in the #new members
thread at the Lean chat at https://leanprover.zulipchat.com (real name preferred).

To prove the next lemma, try using induction on `c`. Once you've done it, 
you can move on to the next page of this level.

-/
/- Lemma
On the set of natural numbers, addition is associative.
In other words, for all natural numbers $a, b$ and $c$, we have
$$ (a + b) + c = a + (b + c). $$
-/
lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin [less_leaky]
  induction c with d hd,
  { -- ⊢ a + b + 0 = a + (b + 0)
    rw add_zero,
    rw add_zero,
    refl
  },
  { -- ⊢ (a + b) + succ d = a + (b + succ d)
    rw add_succ,
    rw add_succ,
    rw add_succ,
    rw hd,
    refl,
  }
end

/-
Once you have associativity, let's move on to commutativity! Click "Next Page" in the top right.
-/
end mynat -- hide 



-/


end mynat