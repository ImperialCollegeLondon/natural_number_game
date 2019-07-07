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

end mynat