import game.world8.level6

def ne_iff_imp_false (a b : mynat) : a ≠ b ↔ ((a = b) → false) := iff.rfl -- hide
/- Axiom : iff_imp_false (a b : mynat) :
a ≠ b ↔ ((a = b) → false)
-/

/-
 * `ne_iff_imp_false (a b : mynat) : (a ≠ b) ↔ ((a = b) → false)

This means that `rw ne_iff_imp_false` will change all our `≠` to implications,
and the tools we already have will be able to deal with them.
-/
