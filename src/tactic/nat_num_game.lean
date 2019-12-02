-- Many many thanks to Rob Lewis for supplying 99.9% of this file.

import tactic.modded tactic.apply

open tactic

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `nat_num_game.interactive

@[reducible] meta def filter (d : declaration) : bool :=
d.to_name ∉ [`tactic.interactive.induction, 
             `tactic.interactive.cases, 
             `tactic.interactive.rw, 
             `tactic.interactive.symmetry,
             `tactic.interactive.use]

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive ∧ filter dec) (copy_decl dec)

@[reducible] meta def nat_num_game := tactic

namespace nat_num_game

--meta instance : monad nat_num_game := by delta nat_num_game; apply_instance

--meta instance : alternative nat_num_game := by delta nat_num_game; apply_instance

meta def step {α} (c : nat_num_game α) : nat_num_game unit := 
c >> return ()

meta def istep := @tactic.istep

meta def save_info := tactic.save_info

meta def execute (c : nat_num_game unit) : nat_num_game unit := 
c

meta def execute_with := @smt_tactic.execute_with
--meta def trace_state {α : Type}

meta def solve1 := @tactic.solve1

end nat_num_game

--#check tactic.interactive.induction

namespace nat_num_game.interactive

meta def induction
:= tactic.interactive.induction'

meta def cases
:= tactic.interactive.cases'

meta def rw
:= tactic.interactive.rw'

meta def symmetry
:= tactic.interactive.symmetry'

meta def use
:= tactic.interactive.use'

end nat_num_game.interactive

run_cmd copy_decls

--TODO : why is this broken?
--#print tactic.interactive.rintro

--#exit

-- example just to check it's running
-- example (n : ℕ) : true :=
-- begin [nat_num_game]
--   induction n,
--     sorry, sorry  
-- end
