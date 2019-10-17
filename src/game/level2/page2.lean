import mynat.definition -- Imports the natural numbers. -- hide
import mynat.add -- definition of addition -- hide
namespace mynat -- hide

/-
Reminder: we have `0 : mynat` and `succ : mynat → mynat`. 
We have these theorems: 
* `zero_ne_succ: ∀ a, zero ≠ succ a`
* `succ_inj : succ a = succ b → a = b`
* `add_zero : ∀ a, a + 0 = a`
* `add_succ : ∀ a b, a + succ(b) = succ(a+b)`

We're going to start by proving the lemma that `∀ n, 0 + n = n`.

Let me guide you through this first proof.
We will see the four tactics `induction`, `exact`, 
`rw` (rewrite) and `refl` in action. Those four tactics
will take us a long way through this game.
But first let's talk about the maths side of things.

Even though we know `n + 0 = n` for all `n`
(that's the theorem `add_zero`, which we have), we
can't deduce that `0 + n = n` because we are
nowhere near proving that `x + y = y + x` yet! 
We will have to prove `0 + n = n` by induction on `n`.

You can start proving by clicking on the button just below that
says "Click here to prove !". 
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
Now highlight the text box, delete `sorry`, and replace it with 

`induction n with d hd,`

*Don't forget the comma*. You'll see what `d` and `hd` are in a second.

When Lean has finished compiling, we now have two goals.
The first is the base case `0 + 0 = 0`.
Let's get rid of that first. This theorem can be proved
using the theorem `add_zero` with the input variable `a` set to zero.
So the next line of your proof should be

`exact add_zero 0,`

(don't forget the comma) and this goal should disappear.

We now have to do the inductive step. As you can see on the right,
we have a natural number `d`, and the inductive hypothesis `hd : 0 + d = d`. 
Our goal is to prove `0 + succ d = succ d`. 

To prove this, we need to use `add_succ`. We know that `add_succ 0 d`
is the result that 0 + succ d = succ (0 + d), so the first thing
we need to do is to replace the left hand side `0 + succ d` of our
goal with the right hand side. We do this with the `rw` command
(`rw` means `rewrite`). Type 

`rw add_succ 0 d,`

(don't forget the comma). The goal will change to

`⊢ succ (0 + d) = succ d`

Now remember our hypothesis `hd : 0 + d = d`. We need
to rewrite this too! Type 

`rw hd,`

(don't forget the comma). The goal will now change to

`⊢ succ d = succ d`

This goal can be solved with the `refl` tactic; `refl`
is, as you can imagine, short for "equality is reflexive",
which is a fancy way of saying "x=x". So finish the proof
with 

`refl,`

and Lean will inform you that there are no goals left. You are done!
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