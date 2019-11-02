import mynat.definition -- Imports the natural numbers. -- hide
import mynat.mul -- hide
namespace mynat -- hide

/-

# World 1: Tutorial world

## level 2: the `exact` tactic.

Delete the `sorry` below and let's look at the box
on the top right. It should look like this:

```
a b : mynat,
h : 2 * a = b + 7
⊢ 2 * a = b + 7
```

So here `a` and `b` are natural numbers,
we have a hypothesis `h` that `2 * a = b + 7` (think of
`h` as a *proof* that `2 * a = b + 7`), and our
goal is to prove that `2 * a = b + 7`. 

Unfortunately `refl` won't work here. `refl` proves things like `3 = 3` or `x + y = x + y`.
`refl` works when both sides of an equality are *exactly the same strings of characters
in the same order*. The reason why `2 * a = b + 7` is true is *not* because `2 * a` and `b + 7`
are exactly the same strings of characters in the same order. The reason it's true is
because it's a hypothesis. The numbers `2 * a` and `b + 7` are equal because of a theorem,
and the proof of the theorem is `h`.  That's what a hypothesis
is -- it's a way of saying "imagine we have a proof of this".

We're hence in a situation where we have a hypothesis `h`,
which is *exactly* equal to the goal we're trying to prove. In
this situation, the tactic

`exact h,`

will close the goal. Try typing `exact h,` where the `sorry` was, and
hit enter after the comma to go onto a new line. 
**Don't forget the `h`** and
**don't forget the comma.**
You should see the "Proof complete!" message, and the error
in the bottom right goal will disappear. The reason
this works is that `h` is *exactly* a proof of the goal.
-/

/- Lemma : no-side-bar
For all natural numbers $a$ and $b$,
if $2a=b + 7$, then $2a=b+7$.
-/
lemma example2 (a b : mynat) (h : 2 * a = b + 7): 2 * a = b + 7 :=
begin [less_leaky]
  exact h



end

/- Tactic : exact
If your goal is a proposition and you have access to a proof
of that proposition, either because it is a hypothesis `h`
or because it is a theorem which is already proved, then

`exact h,`

or

`exact <name_of_theorem>,`

will close the goal. 

### Examples

1) If the top right box (the "local context") looks like
this:

```
x y : mynat
h : y = x + 3
⊢ y = x + 3
```

then

`exact h,`

will close the goal.

2) (from world 2 onwards) If the top right box looks like this:

```
a b : mynat
⊢ a + succ(b) = succ(a + b)
```

then 

`exact add_succ a b,`

will close the goal.
-/

/-
These two tactics, `refl` and `exact`, clearly only
have limited capabilities by themselves. The next
tactic we will learn, the rewrite tactic `rw`, is far more powerful.
Click on "next level" to move onto the next level in tutorial world.
-/
end mynat -- hide 