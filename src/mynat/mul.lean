import mynat.add

namespace mynat

def mul : mynat → mynat → mynat
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul mynat := ⟨mul⟩
-- notation a * b := mul a b

example : (1 : mynat) * 1 = 1 := 
begin
refl
end


lemma mul_zero (m : mynat) : m * 0 = 0 := rfl

lemma mul_succ (m n : mynat) : m * (succ n) = m * n + m := rfl

end mynat