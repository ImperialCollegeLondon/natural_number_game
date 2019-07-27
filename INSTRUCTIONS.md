Here are the instructions.

To start off playing this game, you need to know the following theorems
about "mynat", the natural numbers we are building:

zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)
succ_inj : ∀ {a b : mynat}, succ(a) = succ(b) → a = b
add_zero : ∀ a : mynat, a + 0 = a
add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)

Some occasionally useful other results are:

one_eq_succ_zero : 1 = succ 0
ne_iff_implies_false : a ≠ b ↔ (a = b) → false

You also need to know that the principle of mathematical induction works.

To play, you will also need to know at least some of the following tactics:

exact
assumption
refl
induction
cases
rw (and rw ... at ...)
symmetry
split
intro
revert
apply
exfalso

You can learn about them in the file tactics.md .

Then the idea is that you open the file Assignments/natural_number_game/src/my_solutions/world1_addition.lean

(or one of the other files in there if you're interested in exploring more)

and you edit the file and fill in the sorrys. Note that original sorried file is in src/levels and KMB's "official" solutions are in src/solutions.