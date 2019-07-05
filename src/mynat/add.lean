import mynat.definition

/- 
  mynat/add.lean
  
-/
namespace mynat

-- definition of "addition on the natural numbers"
def add : mynat → mynat → mynat
| m 0 := m
| m (succ n) := succ (add m n)

instance : has_add mynat := ⟨mynat.add⟩

-- numerals now work
example : mynat := 37

lemma add_zero (m : mynat) : m + 0 = m := rfl

lemma add_succ (m n : mynat) : m + succ n = succ (m + n) := rfl

-- end of definition of "addition on the natural numbers"

end mynat
