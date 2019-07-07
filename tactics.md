Tactics
=======

exact
-----

`exact H` : This tactic will close a goal equal to the type of `H`.

Example 1:

```
H : x = y + 1
⊢ x = y + 1
```
The `exact H` tactic will close that goal.

Example 2:
```
H : a + r = b + r → a = b
⊢ a + r = b + r → a = b
```

The tactic `exact H` will close that goal.

Example 3:

```
⊢ succ a ≠ 0
```

The tactic `exact zero_ne_succ a` will close that goal, because `zero_ne_succ a` is a proof that `succ a ≠ 0`.

assumption
----------

This tactic is a variant of `exact`, which closes any goal for which there is already a proof in our assumptions. For example if the assumptions and goal look like this:

```
H : x = y + 1
⊢ x = y + 1
```

then the `assumption` tactic will close this goal.

refl
----

The `refl` tactic will close any goal of the form `a = a`, and more generally any goal of the form `x R x` if `R` is a binary relation which is reflexive.


induction'
----------

`induction' n with d hd`

Does induction on `n`. Assumes that `n` is the kind of thing you can do induction on (for example `n : mynat` would be a great example).

Induction a with d hd

Changes goal from
```
1 goal
P : mynat → Prop,
n : mynat
⊢ P n
```

to

```
2 goals
case mynat.zero
P : mynat → Prop
⊢ P 0

case mynat.succ
P : mynat → Prop,
d : mynat,
hd : P d
⊢ P (succ d)
```

Example:

`induction' n with d Hd,`

takes

```
1 goal
n : mynat
⊢ 0 + n = n
```

to

```
2 goals
case mnat.zero
⊢ 0 + 0 = 0

case mynat.succ
d : mynat,
Hd : 0 + d = d
⊢ 0 + succ d = succ d
```

Note: Lean's usual tactic is `induction`; this modified tactic is less "leaky" -- you won't see random `zero`'s where you are expecting `0`'s.

rw'
---

Does a "rewrite". If `H : a = b` then `rw' H` changes all `a`'s in the goal to `b`'s.

Variant: if you want to change all `b`'s to `a`'s then `rw' ←H` works (use `\l` to get the left arrow)

Variant: if you want to change all `a`'s to `b`'s in hypothesis `H2` then `rw' H at H2` works.

Example:
```
H : a = b + 3
⊢ 0 + a = a + b
```

Then `rw H` changes the goal to

```
⊢ 0 + (b + 3) = b + 3 + b
```

Note: Lean's `rw` tactic tries to close the goal with `refl` after a rewrite; the modified `rw'` tactic does not do this.


symmetry
--------

The `symmetry` tactic will change a goal of the form `a = b` to the goal `b = a`. It will also change a goal of the form `a ≠ b` to a goal of the form `b ≠ a`.

split
-----

The `split` tactic will change a goal of the form `P ∧ Q` into two goals `P` and `Q`. It will also change a goal of the form `P ↔ Q` into two goals `P` and `Q`.

Note that when two goals are created, it is considered best practice to deal with each goal separately in `{ }` brackets. For example if the assumptions and goal look like this:

```
P Q : Prop,
hpq : P → Q,
hqp : Q → P
⊢ P ↔ Q
```

then a proof might look like this:

```
  split,
  {
    exact hpq
  },
  {
    exact hqp
  }
```

intro
-----

The `intro` tactic can be used when the goal looks like `P → Q` or like `∀ x, f x = g x`.

In the `P → Q` case, `intro HP` turns

```
⊢ P → Q
```

to

```
HP : P
⊢ Q
```

and in the `∀ x, f x = g x` case, `intro a` turns
```
⊢ ∀ (x : ℕ), f x = g x
```

to

```
a : ℕ
⊢ f a = g a
```

A variant: the `intros` tactic will introduce more than one variable at once. For example if the state is

```
⊢ ∀ (x y : ℕ), f x y = g x y
```

then `intros a b` turns it into

```
a b : ℕ
⊢ f a b = g a b
```

revert
------

The `revert` tactic does the opposite of the `intro` tactic. For example if the state is

```
a : ℕ
⊢ f a = g a
```

then `revert a` will transform it to


```
⊢ ∀ (a : ℕ), f a = g a
```

apply
-----

If the assumptions and goal look like this:

```
H : P → Q
⊢ Q
```

then the tactic `apply H` will change the goal to `⊢ P`.

As a more clever application, `succ_inj` is a proof of
`∀ (m n : ℕ), succ m = succ n → m = n`. If the goal is

```
⊢ a = b
```

then `apply succ_inj` will transform it to

```
⊢ succ a = succ b
```

exfalso
-------

The `exfalso` tactic changes any goal at all to `false`. This is often used when the assumptions are contradictory (e.g. during a proof by contradiction).

Example of usage: if the assumptions and goal are this:

```
hP : P,
hnP : P → false
⊢ Q
```

then a proof could be

```
  exfalso,
  apply hnP,
  exact hP
```



***

