import game.world8.level12 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 13: `ne_succ_self`

The last level in Advanced Addition World is the statement
that $n\not=\operatorname{succ}(n)$. When you've done this
you've completed Advanced Addition World and can move on
to Advanced Multiplication World (after first doing
Multiplication World, if you didn't do it already). 
-/

/- Lemma
For any natural number $n$, we have
$$ n \neq \operatorname{succ}(n). $$
-/
lemma ne_succ_self (n : mynat) : n ≠ succ n :=
begin [nat_num_game]
  induction n with d hd,
    apply zero_ne_succ,
  intro hs,
  apply hd,
  apply succ_inj,
  assumption


end

end mynat -- hide
