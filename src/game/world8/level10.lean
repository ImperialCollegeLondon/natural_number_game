import game.world8.level9 -- hide
namespace mynat -- hide

/-
# Advanced Addition World

## Level 10: `add_left_eq_zero`

## Important: the definition of `≠`

In Lean, `a ≠ b` is *defined to mean* `(a = b) → false`. 
This means that if you see `a ≠ b` you can *literally treat
it as saying* `(a = b) → false`. Computer scientists would
say that these two terms are *definitionally equal*. 

The following lemma will be useful in inequality world.
Let me go through the proof, because it introduces several new
concepts: 

* `cases b` with `b : mynat`
* `exfalso`
* `apply succ_ne_zero`

We're going to prove $a+b=0\implies b=0$. Here is the
strategy. Each natural number is either `0` or `succ(d)` for
some other natural number `d`. So we can start the proof
with 

`cases b with d,`

and then we have two cases. The first you can solve easily.
The second looks like this:

```
a d : mynat,
H : a + succ d = 0
⊢ succ d = 0
```

Our goal is impossible to prove. However our hypothesis `H`
is also impossible, meaning that we still have a chance!
First let's see why `H` is impossible. We can

`rw add_succ at H,`

to turn `H` into `H : succ (a + d) = 0`. Because
`succ_ne_zero (a + d)` is a proof that `succ (a + d) ≠ 0`,
it is also a proof of the implication `succ (a + d) = 0 → false`.
Hence `succ_ne_zero (a + d) H` is a proof of `false`!
Unfortunately our goal is not `false`, it's a generic
false statement. 



-/

/- Lemma
If $a$ and $b$ are natural numbers such that 
$$ a + b = 0, $$
then $b = 0$.
-/
lemma add_left_eq_zero {a b : mynat} (H : a + b = 0) : b = 0 :=
begin [less_leaky]
  cases b with d,
  { refl},
  { rw add_succ at H,
    exfalso,
    apply zero_ne_succ (a + d),
    rw H,
    refl,
  },
end

end mynat -- hide
