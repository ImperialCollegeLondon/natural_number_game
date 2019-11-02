import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level6andthreequarters -- hide
namespace mynat -- hide

/- Tactic : intro
The `intro h` tactic is very simple. If we're trying to prove
$P\implies Q$ with $P$ and $Q$ true/false statements, then
`intro h` is Lean's way of saying "Let's assume $P$ is true,
and let's call its proof `h`".

More formally, the `intro` tactic makes progress if the *goal*
is an *implication*. For example, say our local context looks like this:

```
a b : mynat
⊢ a + a = b + b → a + b
```

Then after `intro h` it will look like this:

```
a b : mynat,
h : a + a = b + b
⊢ a = b
```

-/

/-

# World 2 -- Addition World

## Level 6 and seven eighths:  -- `succ_eq_succ_of_eq`.
-/

/-
Here we will learn the `intro` tactic. We are going to prove something
completely obvious: if $a=b$ then $succ(a)=succ(b)$. This is *not* `succ_inj`!
This is trivial -- we can just rewrite our proof of `a=b`.
But how do we get to that proof?
-/

/- Theorem
For all naturals $a$ and $b$, $a=b\implies succ(a)=succ(b)$. 
-/
theorem succ_eq_succ_of_eq {a b : mynat} : a = b → succ(a) = succ(b) :=
begin [less_leaky]
  intro h,
  rw h,
  refl,
end

/-
Try starting with

`intro h,`

Now `rw` and `refl` will get you home.
-/
end mynat -- hide