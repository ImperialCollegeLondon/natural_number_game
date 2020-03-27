import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level6 -- hide
namespace mynat -- hide

/- Axiom : succ_inj {a b : mynat} :
  succ(a) = succ(b) → a = b
-/

/-

# Advanced Addition World

## Level 1: `succ_inj`. A function.

Peano's original collection of axioms for the natural numbers contained two further
assumptions, which have not yet been mentioned in the game:

```
succ_inj {a b : mynat} :
  succ(a) = succ(b) → a = b

zero_ne_succ (a : mynat) :
  zero ≠ succ(a)
 ```

The reason they have not been used yet is that they are both implications,
that is,
of the form $P\implies Q$. This is clear for `succ_inj a b`, which
says that for all $a$ and $b$ we have $succ(a)=succ(b)\implies a=b$.
For `zero_ne_succ` the trick is that `X ≠ Y` is *defined to mean*
$X = Y\implies{\tt false}$. If you have played through Proposition world,
you now have the required Lean skills (i.e., you know the required
tactics) to work with these implications.
Let's finally learn how to use `succ_inj`. You should know a couple
of ways to prove the below -- one directly using an `exact`, and one which uses an
`apply` first.
-/

/- Theorem : no-side-bar
For all naturals $a$ and $b$, if we assume $succ(a)=succ(b)$, then we can
deduce $a=b$. 
-/
theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b := 
begin [nat_num_game]
    exact succ_inj(hs),



end

/-
## Important thing.

You can rewrite proofs of *equalities*. If `h : A = B` then `rw h` changes `A`s to `B`s.
But you *cannot rewrite proofs of implications*. `rw succ_inj` will *never work*
because `succ_inj` isn't of the form $A = B$, it's of the form $A\implies B$.
-/
end mynat -- hide
