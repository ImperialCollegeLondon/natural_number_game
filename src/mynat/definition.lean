import tactic.modrw -- rw' is rw with no refl at the end
import tactic.structure_helper

/-

  mynat/definition.lean -- definition of mynat.
  
  Supplies:
  constants zero : mynat and one : mynat
  function S : mynat → mynat
  notation 0 for zero and 1 for one.

The below code will be *invisible to the player*
-/

-- definition of "the natural numbers"
inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

namespace mynat

instance : has_zero mynat := ⟨mynat.zero⟩

--meta def tidy_zeros : tactic unit := do
--`[repeat {all_goals {rw (show mynat.zero = (0 : mynat), from rfl) at *}}]

def one : mynat := succ 0

instance : has_one mynat := ⟨mynat.one⟩

lemma zero_ne_succ (m : mynat) : (0 : mynat) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : mynat} (h : succ m = succ n) : m = n := by cases h; refl

end mynat

namespace tactic.interactive

open tactic.interactive interactive.types expr lean lean.parser tactic interactive

meta def induction' (hp : parse cases_arg_p) (ids : parse with_ident_list) : tactic unit :=
do tactic.interactive.induction hp none ids none,
all_goals `[
  try {rw' (show mynat.zero = (0 : mynat), from rfl) at *},
  try {change mynat.le with (≤) at *}]
--  try {change @mynat.succ with (λ n, n + 1) at *, dsimp only at *}]

meta def cases' : parse cases_arg_p → parse with_ident_list → tactic unit
| (none,   p) ids := do
  e ← i_to_expr p,
  cases_core e ids,
  all_goals `[
  try {rw' (show mynat.zero = (0 : mynat), from rfl) at *},
  try {change mynat.le with (≤) at *}]
| (some h, p) ids := do
  x   ← get_unused_name,
  generalize h () (p, x),
  hx  ← get_local x,
  cases_core hx ids,
  all_goals `[
  try {rw' (show mynat.zero = (0 : mynat), from rfl) at *},
  try {change mynat.le with (≤) at *}]



end tactic.interactive

attribute [symm] ne.symm
