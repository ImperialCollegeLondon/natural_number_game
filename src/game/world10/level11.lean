import game.world10.level10 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 11: `add_le_add_right`

If you're faced with a goal of the form `forall t, ...`, then the next
line is "so let $t$ be arbitrary". The way to do this in Lean is `intro t`.
-/

/- Lemma
For all naturals $a$ and $b$, $a\le b$ implies that for all naturals $t$,
$a+t\le b+t$.
-/
theorem add_le_add_right (a b : mynat) : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin [less_leaky]
  intro h,
  cases h with c hc,
  intro t,
  use c,
  rw hc,
  ring,

  
end

end mynat -- hide
