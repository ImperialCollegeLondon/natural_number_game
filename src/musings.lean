#exit
#check @lt_of_add_lt_add_left
#check canonically_ordered_comm_semiring.lt_of_add_lt_add_left

structure thingo :=
(func : Π (a : ℕ), ℕ)

-- works
def foo : thingo := {func := λ {a : ℕ}, a + 1}

-- also works!
def concrete {{a : ℕ}} : ℕ := a + 1

def bar : thingo := {func := concrete}

/-
canonically_ordered_comm_semiring
  canonically_ordered_monoid, 
    ordered_comm_monoid
      add_comm_monoid
      partial_order
    lattice.order_bot
      partial_order
  comm_semiring
  zero_ne_one_class


-/
