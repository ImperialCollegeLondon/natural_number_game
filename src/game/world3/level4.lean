import game.world3.level3 -- hide
namespace mynat -- hide

/-
# Multiplication World

## Level 4: `mul_add`

Currently our tools for multiplication include the
following: 

* `mul_zero m : m * 0 = 0`
* `zero_mul m : 0 * m = 0`
* `mul_succ a b : a * succ b = a * b + a`

but for addition we have `add_comm` and `add_assoc`
and are in much better shape.

Where are we going? Well we want to prove `mul_comm`
and `mul_assoc`, i.e. that `a * b = b * a` and
`(a * b) * c = a * (b * c)`. But we *also* want to
establish the way multiplication interacts with addition,
i.e. we want to prove that we can "expand out the brackets"
and show `a * (b + c) = (a * b) + (a * c)`.
The technical term for this is "distributivity of multiplication over addition".

Note the name of this lemma -- `mul_add`. And note the left
hand side -- `a * (b + c)`, a multiplication and then an addition.
I think `mul_add` is much easier to remember than "distributivity". 
-/

/- Lemma
Multiplication is distributive over addition.
In other words, for all natural numbers $a$, $b$ and $t$, we have
$$ t(a + b) = ta + tb. $$
-/

lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
begin [less_leaky]
  induction b with d hd,
  { rewrite [add_zero, mul_zero, add_zero],
  },
  {
    rw add_succ,
    rw mul_succ,
    rw hd,
    rw mul_succ,
    rw add_assoc, -- ;-)
    refl,


  }
end

def left_distrib := mul_add -- stupid field name,          -- hide
-- I just don't instinctively know what left_distrib means -- hide

end mynat -- hide
