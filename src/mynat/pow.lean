import mynat.mul

namespace mynat

def pow : mynat → mynat → mynat
| m zero := one
| m (succ n) := pow m n * m

instance : has_pow mynat mynat := ⟨pow⟩
-- notation a ^ b := pow a b

example : (1 : mynat) ^ (1 : mynat) = 1 := 
begin
refl
end

lemma pow_zero (m : mynat) : m ^ (0 : mynat) = 1 := rfl

lemma pow_succ (m n : mynat) : m ^ (succ n) = m ^ n * m := rfl

end mynat