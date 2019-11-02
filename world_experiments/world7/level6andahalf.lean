import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level6 -- hide
namespace mynat -- hide


/-

# World 2 -- Addition World

## Level 6 and a half:  -- `succ_inj`. A function.

If you're playing this level, you have decided against
collectible-hunting and are looking to learn something else.
When we stated Peano's axioms I mentioned two things which
we have never used:

```
succ_inj (a b : mynat) :
  succ(a) = succ(b) → a = b

zero_ne_succ (a : mynat) :
  zero ≠ succ(a)
 ```

I tucked these facts away because they are both implications. They are
of the form $P\implies Q$. This is clear for `succ_inj a b`, which
says that for all $a$ and $b$ we have $succ(a)=succ(b)\implies a=b$.
For `zero_ne_succ` the trick is that you can turn `X ≠ Y` into
$X = Y\implies$ `false`. The reason we have not used these facts so far
is that we do not have the required skills to work with implications.
Let's finally learn how to use `succ_inj`.
-/

/- Theorem
For all naturals $a$ and $b$, if we assume $succ(a)=succ(b)$, then we can
deduce $a=b$. 
-/
theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b := 
begin [less_leaky]
    exact succ_inj(hs),



end

/-
You can rewrite proofs of equalities. If `h : A = B` then `rw h` changes `A`s to `B`s.
But you *cannot rewrite proofs of implications*. `rw succ_inj` doesn't work
because `succ_inj` isn't `A = B`, it's $A\implies B$.

One way you can prove this level is

`exact succ_inj(hs),`

. What is happening here is
that we are thinking of `succ_inj` as a function which takes a proof of `succ(a) = succ(b)`
and spits out a proof of `a = b`. We feed `hs` (a proof that `succ(a)=succ(b)`) into
the `succ_inj` function and the output is a proof that `a = b`, so we can use
the `exact` tactic to finish our goal. 

In the next level we will see how to create and prove an auxiliary hypothesis
right in the middle of another proof, using the `have` tactic.
-/
end mynat -- hide