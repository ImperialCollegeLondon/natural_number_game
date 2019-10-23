import game.world5.level4 -- hide
namespace mynat -- hide

/-
# World 5 : Inequality world 

## Level 5 : `le_trans`
-/

/- Lemma
≤ is transitive. In other words, if a ≤ b and b ≤ c then a ≤ c. 
-/
theorem le_trans ⦃a b c : mynat⦄ (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin [less_leaky]
  cases hab with d hd,
  cases hbc with e he,
  use (d + e),
  rw ←add_assoc,
  rw ←hd,
  assumption,


end

/-
Congratulations -- you just proved that the natural numbers are a preorder.
-/
instance : preorder mynat := by structure_helper -- hide
end mynat -- hide
