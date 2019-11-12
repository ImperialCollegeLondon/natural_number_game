import game.world10.level4 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 5: `le_trans`

Another straightforward one. 
-/


/- Lemma
≤ is transitive. In other words, if $a\leq b$ and $b\leq c$ then $a\leq c$. 
-/
theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin [less_leaky]
  cases hab with d hd,
  cases hbc with e he,
  use (d + e),
  rw ←add_assoc,
  rw ←hd,
  assumption,
end

/-
Congratulations -- you just got a collectible. You proved that the
natural numbers are a preorder.
-/
instance : preorder mynat := by structure_helper
end mynat -- hide
