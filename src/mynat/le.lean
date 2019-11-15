import mynat.mul

-- this is one of *three* routes to
-- canonically_ordered_comm_semiring

namespace mynat

def le (a b : mynat) :=  ∃ (c : mynat), b = a + c

-- Another choice is to define it recursively: 
-- | le 0 _
-- | le (succ a) (succ b) = le ab 

-- notation
instance : has_le mynat := ⟨mynat.le⟩

@[leakage] theorem le_def' : mynat.le = (≤) := rfl

theorem le_iff_exists_add (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c := iff.rfl

end mynat