import game.world10.level17 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 18: lt_of_add_lt_add_left

Two collectibles for the price of one: after the below lemma
we can deduce both that the naturals are an ordered commutative
monoid and a canonically-ordered monoid ("canonical" here means
that $a\le b$ if and only if there exists $c$ with $b=a+c$, plus
some other axioms).
-/

/- Lemma : 
For all naturals $a$ $b$ and $c$, 
$$a+b<a+c\implies b<c.$$ 
-/
lemma lt_of_add_lt_add_left (a b c : mynat) : a + b < a + c → b < c :=
begin [less_leaky]
  rw lt_iff_succ_le,
  rw lt_iff_succ_le,
  intro h,
  apply le_of_add_le_add_left, -- wtf? Not there?
end

def bot := 0 -- hide
def bot_le := zero_le -- hide
instance : canonically_ordered_monoid mynat := by structure_helper
instance : ordered_comm_monoid mynat := by structure_helper

end mynat -- hide
