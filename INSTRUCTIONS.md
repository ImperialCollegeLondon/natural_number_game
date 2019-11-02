# Playing the game.

## Note

Note: these are sketchy instructions for playing
the version of the game where you install Lean
and mathlib. If you just want to play online
without installing anything, then
[here's the link](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/).

## After installation

If you open the file `src/my_solutions/world1_addition.lean` then you will see plenty of `sorry`s. You will currently also see a lot of comments which need editing and possibly completely removing and putting here instead.

This whole thing is currently very daunting because the game is in a very preliminary state. This will be fixed up later. The general idea is that every `sorry` in the file `world1_addition.lean` needs to be removed and replaced with a proof. We will go through an example of how this works at the bottom of this file.



To start off playing this game, you need to know the following theorems
about "mynat", the natural numbers we are building:

zero_ne_succ : ∀ a : mynat, zero ≠ succ(a)
succ_inj : ∀ a b : mynat, succ(a) = succ(b) → a = b
add_zero : ∀ a : mynat, a + 0 = a
add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)

Some occasionally useful other results are:

one_eq_succ_zero : 1 = succ 0
ne_iff_implies_false : a ≠ b ↔ ((a = b) → false)

You also need to know that the principle of mathematical induction works.

To play, you will also need to know at least some of the following Lean tactics:

```
exact
assumption
refl
induction
cases
rw (and rw ... at ...)
symmetry
split
intro
revert
apply
exfalso
```

## Worked solution of first level.

The first level is this:

```
lemma zero_add (n : mynat) : 0 + n = n :=
begin [less_leaky]
  sorry
end
```

and the object is to replace the `sorry` with a proof. Whatever is going on here? Well, as we should clearly explain somewhere, addition on the natural numbers is *defined* in the following way:

1) `x + 0 = x`
2) If `x + y` is already defined and equals `n`, then `x + succ(y)` is defined to be `succ(n)`. Here `succ(y)` means the number after `y`.

If you think about it, you'll see that we have defined `x + y` for all natural numbers `y` -- the proof is by induction.

*By definition*, `x + 0 = x`. This fact has a name, it's called `add_zero x`.

However it is *not* true that *by definition* `0 + x = x`. This is a theorem, which needs to be proved by induction on `x`. Here is a full proof.

lemma zero_add (n : mynat) : 0 + n = n :=
begin [less_leaky]
  -- put your cursor here -- you can see the goal, `⊢ 0 + n = n` . The `⊢` symbol
  -- means "this is what needs to be proved". If you can't see the goal 0 + n = n
  -- in a separate window on the right hand side of VS Code, press Ctrl+Shift+Enter
  -- to open VS Code's "info view".
  induction n with d hd,
    -- There are now two goals (so I indented a little). The first is the base case 0 + 0 = 0, and the
    -- second is the inductive step, where we have a hypothesis hd : 0 + d = d
    -- and our goal is to prove `0 + succ(d) = succ(d)`. 


    -- the base case goal is easy. We know that x + 0 = 0 -- this is called `add_zero` -- and
    -- we can rewrite this theorem
    rw add_zero,
    -- and our goal now becomes 0 = 0.
    refl, -- this tactic solves all goals of the form x = x. 
  
  -- We're now back to one goal, the inductive step. The inductive step goal is a little trickier. 
  -- The goal is 0 + succ(d) = succ(d). But `add_succ` is a theorem which says that x + succ(y) = succ(x + y),
  -- and this theorem is true *by definition of addition*. Let's use this theorem.
  rw add_succ,
  -- our goal is now to prove succ(0 + d) = succ d. But our hypothesis hd says 0 + d = d, so we can
  -- replace 0 + d with d by using a rewrite.
  rw hd,
  -- the goal is now succ(d) = succ(d) which we can prove with refl.
  refl
end

## More instructional materials.

[Shoddy notes of mine](http://wwwf.imperial.ac.uk/~buzzard/xena/html/source/ch1_and_or_props/prop_exercises.html)

The very wonderful [Theorem Proving In Lean](https://leanprover.github.io/theorem_proving_in_lean/), especially [chapter 5 on tactics](https://leanprover.github.io/theorem_proving_in_lean/tactics.html)

The [blog post](https://xenaproject.wordpress.com/2017/10/31/building-the-non-negative-integers-from-scratch/) which started me thinking about all this.
