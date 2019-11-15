import mynat.le

namespace mynat

def lt (a b : mynat) := a ≤ b ∧ ¬ (b ≤ a)

-- notation
instance : has_lt mynat := ⟨mynat.lt⟩

@[leakage] theorem lt_def' : mynat.lt = (<) := rfl

end mynat