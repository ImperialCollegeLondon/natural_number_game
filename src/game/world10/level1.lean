import mynat.le -- import definition of ≤
import game.world9.level4
import game.world4.level8
namespace mynat -- hide
/- Axiom : le_iff_exists_add (a b : mynat)
  a ≤ b ↔ ∃ (c : mynat), b = a + c
-/

/- Tactic : use
## Summary

`use` works on the goal. If your goal is `⊢ ∃ c : mynat, 1 + x = x + c`
then `use 1` will turn the goal into `⊢ 1 + x = x + 1`, and the rather
more unwise `use 0` will turn it into the impossible-to-prove
`⊢ 1 + x = x + 0`.

## Details

`use` is a tactic which works on goals of the form `⊢ ∃ c, P(c)` where
`P(c)` is some proposition which depends on `c`. With a goal of this
form, `use 0` will turn the goal into `⊢ P(0)`, `use x + y` (assuming
`x` and `y` are natural numbers in your local context) will turn
the goal into `P(x + y)` and so on.
-/

-- World name : Inequality world
/- 

# Inequality world. 

A new import, giving us a new definition. If `a` and `b` are naturals,
`a ≤ b` is *defined* to mean

`∃ (c : mynat), b = a + c`

The upside-down E means "there exists". So in words, $a\le b$
if and only if there exists a natural $c$ such that $b=a+c$. 

If you really want to change an `a ≤ b` to `∃ c, b = a + c` then
you can do so with `rw le_iff_exists_add`:

```
le_iff_exists_add (a b : mynat) :
  a ≤ b ↔ ∃ (c : mynat), b = a + c
```

But because `a ≤ b` is *defined as* `∃ (c : mynat), b = a + c`, you
do not need to `rw le_iff_exists_add`, you can just pretend when you see `a ≤ b`
that it says `∃ (c : mynat), b = a + c`. You will see a concrete
example of this below.

A new construction like `∃` means that we need to learn how to manipulate it.
There are two situations. Firstly we need to know how to solve a goal
of the form `⊢ ∃ c, ...`, and secondly we need to know how to use a hypothesi
of the form `∃ c, ...`. 

## Level 1: the `use` tactic.

The goal below is to prove $x\le 1+x$ for any natural number $x$. 
First let's turn the goal explicitly into an existence problem with

`rw le_iff_exists_add,`

and now the goal has become `∃ c : mynat, 1 + x = x + c`. Clearly
this statement is true, and the proof is that $c=1$ will work (we also
need the fact that addition is commutative, but we proved that a long
time ago). How do we make progress with this goal?

The `use` tactic can be used on goals of the form `∃ c, ...`. The idea
is that we choose which natural number we want to use, and then we use it.
So try

`use 1,`

and now the goal becomes `⊢ 1 + x = x + 1`. You can solve this by
`exact add_comm 1 x`, or if you are lazy you can just use the `ring` tactic,
which is a powerful AI which will solve any equality in algebra which can
be proved using the standard rules of addition and multiplication. Now
look at your proof. We're going to remove a line.

## Important

An important time-saver here is to note that because `a ≤ b` is *defined*
as `∃ c : mynat, b = a + c`, you *do not need to write `rw le_iff_exists_add`*.
The `use` tactic will work directly on a goal of the form `a ≤ b`. Just
use the difference `b - a` (note that we have not defined subtraction so
this does not formally make sense, but you can do the calculation in your head).
-/

/- Lemma : no-side-bar
If $x$ is a natural number, then $x\le 1+x$.
-/
lemma one_add_le_self (x : mynat) : x ≤ 1 + x :=
begin
  rw le_iff_exists_add,
  use 1,
  ring,


end 
end mynat -- hide
