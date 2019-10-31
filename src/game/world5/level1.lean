import game.world4.level7 -- hide
import mynat.le
namespace mynat -- hide

-- World name : Inequality world

/- Axiom : le_def (a b : mynat) :
a ≤ b ↔ ∃ c, b = a + c
-/


/- 
# World 5 : Inequality world 

A new level, a new import. By the way, you can take a look at the actual files
being imported by going to the source code for this game,
which is available at
<a href="https://github.com/ImperialCollegeLondon/natural_number_game" target="blank">
GitHub</a>. The game files are in `src/game` and the imports are in `src/mynat`

Here's what you get from the import:

1) The following data:
  * a binary relation called mynat.le, and notation a ≤ b for this relation.

  The definition is: `a ≤ b ↔ ∃ c : mynat, b = a + c`

2) The following axiom:

  * `le_def (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c`

So `rw le_def` will change $a \leq b$ to `∃ c : mynat b = a + c`.

You'll now have to know what to do with terms which have an ∃ in them! There
are two new tactics you'll need immediately, but even with those
we will not be able to get much further -- we really need to learn about 
some sort of Propositions-as-Types thing at some point. But let's press
on anyway by introducing the `use` tactic.

## The `use` tactic. 

If your *goal* is of the form `∃ c, ...` then to make progress you can
use the `use` tactic. Note of course that you have to decide what to use!
You are going to prove a theorem of the form "there exists $c$ such that blahblahblah"
by actually saying "look -- this explicit choice of $c$ works".
For example if your local context is this:
```
x y : mynat
⊢ ∃ c : mynat, c + y = x + y
```

then we want to set `c = x` so we write `use x`, and this will remove the `∃`
and change `t` to `x`, so the goal will become `⊢ x + y = x + y` which you can
solve with `refl`. 

Note that `use` is a tactic that can go wrong -- if you `use` the wrong value
then your goal might become *impossible* to solve and you'll have to go back
and change your mind.
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
## Level 1: `le_refl`

To get started on this level, you can `rw le_def`. Once you have proved
it, we will know that `≤` is reflexive.
-/

/- Lemma
For all naturals $a$, $a \leq a$.
-/
theorem le_refl (a : mynat) : a ≤ a :=
begin [less_leaky]
  rw le_def,
  use 0,
  rw add_zero, 
  refl,

end

/-
Now we write some magical incantation (thanks to Reid Barton
for correcting my spell)...
-/
attribute [refl] mynat.le_refl
/-
...and now the `refl` tactic will close all goals of the form `a ≤ a`
as well as all goals of the form `a = a`.
-/
example : (0 : mynat) ≤ 0 := begin
  refl
end

end mynat --hide
