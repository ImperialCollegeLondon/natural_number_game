import game.world10.level2 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 3: `le_succ_of_le`

We have seen how the `use` tactic makes progress on goals of the form `⊢ ∃ c, ...`.
But what do we do when we have a *hypothesis* of the form `h : ∃ c, ...`?
The hypothesis claims that there exists some natural number `c` with some
property. How are we going to get to that natural number `c`? It turns out
that the `cases` tactic can be used (just like it was used to extract
information from `∧` and `∨` and `↔` hypotheses). Let me talk you through
the proof of $a\le b\implies a\le\operatorname{succ}(b)$.

The goal is an implication so we clearly want to start with 

`intro h,`

. After this, if you *want*, you can do something like

`rw le_iff_exists_add at h ⊢,`

(get the sideways T with `\|-` then space). This changes the `≤` into
its `∃` form in `h` and the goal -- but if you are happy of just *seeing*
the `∃` whenever you read a `≤` then you don't need to do this line.

Our hypothesis `h` is now `∃ (c : mynat), b = a + c` (or `a ≤ b` if you
elected not to do the definitional rewriting) so

`cases h with c hc,`

gives you the natural number `c` and the hypothesis `hc : b = a + c`.
Now use `use` wisely and you're home.

-/

/- Lemma
For all naturals $a$, $b$, if $a\leq b$ then $a\leq \operatorname{succ}(b)$. 
-/
theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) :=
begin [nat_num_game]
  intro h,
  cases h with c hc,
  rw hc,
  use c + 1,
  refl,


end

/-


Did you use `succ c` or `c + 1` or `1 + c`? Those numbers are all
equal, right? So it doesn't matter which one you use, right?

Here's an interesting question. If you copy the proof below into
the box above, and then fill in the `???`
below with `succ c`, will this proof compile? (move your cursor to
after the final comma to see what Lean thinks). What about if you
`use 1 + c`? What about if you `use c + 1`? Can you work out
what is going on? Does it help if I tell you that the *definition*
of `1` is `succ 0`?

```
theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) :=
begin [nat_num_game]
  intro h,
  cases h with c hc,
  rw hc,
  use ???,
  refl,


end
```

-/
end mynat -- hide
