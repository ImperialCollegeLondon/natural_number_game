import game.world4.level7 -- hide
import mynat.le
namespace mynat -- hide

/- A new level, a new import. You can take a look at the actual Leo `an files
being imported by going to the source code for this game,
which is available at
<a href="https://github.com/ImperialCollegeLondon/natural_number_game" target="blank">
GitHub</a>.

Here's what you get from the import:

1) The following data:
  * a binary relation called mynat.le, and notation a ≤ b for this relation.

  The definition is: a ≤ b ↔ ∃ c : mynat, b = a + c

2) The following axiom:

  * `le_def (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c`

So `rw le_def` will change a ≤ b to `∃ c : mynat b = a + c`.

You'll now have to know what to do with terms which have an ∃ in them! There
are two new tactics you'll need.

1) If your *goal* is of the form `∃ c, ...` then to make progress you can
use the `use` tactic. For example if your local context is this:
```
x y : mynat
⊢ ∃ t : mynat, t + y = x + y
```

then we want to set `t = x` so we write `use x`, and this will remove the `∃`
and change `t` to `x`. 

2) If you have a *hypothesis* of the form `h : ∃ c, P` where `P` is some
proposition (which probably depends on `c`) then to extract `c` from `h` you
can use the `cases` tactic. For example, if `h` is as above, then
`cases h with c hc` will create your term `c` as well as creating a proof `hc` of `P`,
i.e., `hc` is the proof that `c` satisfies `P`.

For example, if we have
```
h : ∃ c : mynat, c + c = 12
```

then 

`cases h with c hc`

will turn it into
```
c : mynat,
hc : c + c = 12
```

Of course if you don't want it to be called `c`, you can do `cases h with n hn`
and if you want `n + n = 12` to be called H12 you can do `cases h with n H12`.

-/

/- Tactic : cases
If you have a hypothesis `h : ∃ n, P(n)`
where `P(n)` is a proposition depending on `n`, then
`cases h with d hd`
will produce a new term `d` and also a proof `hd` of `P(d)`. 

## Example

If the local context contains
```
h : ∃ c : mynat, c + c = 12
```

then 

`cases h with c hc`

will turn it into
```
c : mynat,
hc : c + c = 12
```
-/

/- Tactic : use
If your goal is of the form 

```
⊢ ∃ c : P(c)`
```
where `P` is some proposition which depends on `c`, then you might want to prove it
by coming up with an explicit value of `c` for which you can prove `P(c)`. The
way you supply this value is with the `use` tactic. For example if the goal is

```
⊢ ∃ c : c = 6
```

then you can prove this with

```
use 6,
refl,
```

-/

/-

## Level 1/30 or so: `le_refl`

To get started on this level, you can `rw le_def`. Once you have proved
it, the `refl` tactic will close all goals of the form `a ≤ a`.
-/

-- example
theorem le_refl (a : mynat) : a ≤ a :=
begin [less_leaky]
  rw le_def,
  use 0,
  rw add_zero, 
  refl,

end

attribute [_refl_lemma] le_refl -- hide

end mynat --hide
