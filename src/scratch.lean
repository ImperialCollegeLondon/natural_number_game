import tactic.linarith -- any import is fine

inductive mynat
| zero : mynat
| succ : mynat → mynat

namespace mynat

inductive le : mynat → mynat → Prop
| refl (a : mynat) : le a a
| succ {a b : mynat} : le a b → le a (succ b)

-- I never want to see `le` ever ever again.

instance : has_le mynat := ⟨mynat.le⟩

example (a b : mynat) (h : a ≤ b) : a ≤ (succ b) :=
begin
  apply le.succ,
  -- aargh go away le 
  sorry
end

-- idea
def le_succ {a b : mynat} : a ≤ b → a ≤ (succ b) := le.succ

example (a b : mynat) (h : a ≤ b) : a ≤ (succ b) :=
begin
  apply le_succ,
  -- ⊢ a ≤ b
  assumption,
end

example (a b : mynat) {h : a ≤ b} : false :=
begin
  -- cases h, -- aargh it's le again
  -- induction h, -- aargh
  -- rcases h, -- it's still there
  -- I just want a tactic which does the recursion without `le` leaking
  sorry,
end

universe u -- rolls eyes

def le_induction_on :
  -- just rewrite mynat.le.rec using ≤
  ∀ (C : mynat → mynat → Prop),
    (∀ (a : mynat), C a a) →
    (∀ {a b : mynat}, a ≤ b → C a b → C a (succ b)) → -- should a ≤ b be implicit?
    ∀ {a b : mynat}, a ≤ b →
    C a b
:= @mynat.le.rec

#check @mynat.le_induction_on -- looks good

example {P : Prop} {a b : mynat}
(h_refl : ∀ a : my{a b : mynat} (h : a ≤ b) (h_refl : P :=
  @mynat.le.rec
    -- (λ a b, a ≤ b → P)
    _ _ _ _ _ _

#exit
begin
  -- some_tactic h

  -- apply -- something
  
  --two goals


   ∀ P : Prop, 
  apply le_induction_on (λ a b, @h),
  -- cases h, -- aargh it's le again
  -- induction h, -- aargh
  -- rcases h, -- it's still there
  -- I just want a tactic which does the recursion without `le` leaking
  sorry,
end


end mynat

#exit
#check mynat.induction
