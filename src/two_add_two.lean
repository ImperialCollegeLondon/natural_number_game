-- Let's define numbers
inductive number
-- Zero is a number.
| zero : number
-- The "successor" S of a number, is a number.
| S : number → number

open number

#check number
#check zero
#check S

definition one := S (zero)

#check one
#print one

definition two := S (one)
definition three := S (two)
definition four := S (three)

-- Let's define the function which adds n to a number.
definition add_n (n : number) : number → number
-- What do we want n + 0 to be?
| zero := n
-- And if we know n + x already, what do we want n + (number after x) to be?
| (S x) := S (add_n x)

instance : has_add number := ⟨add_n⟩

theorem easy : two + two = four := begin
  refl
end 