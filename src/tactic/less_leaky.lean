-- Many many thanks to Rob Lewis for supplying 99.9% of this file.

import tactic.inductionandcases

open tactic

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `less_leaky.interactive

@[reducible] meta def filter (d : declaration) : bool :=
d.to_name ∉ [`tactic.interactive.induction, `tactic.interactive.cases, `tactic.interactive.rw]

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive ∧ filter dec) (copy_decl dec)

@[reducible] meta def less_leaky := tactic

namespace less_leaky

--meta instance : monad less_leaky := by delta less_leaky; apply_instance

--meta instance : alternative less_leaky := by delta less_leaky; apply_instance

meta def step {α} (c : less_leaky α) : less_leaky unit := 
c >> return ()

meta def istep := @tactic.istep

meta def save_info := tactic.save_info

meta def execute (c : less_leaky unit) : less_leaky unit := 
c

--meta def trace_state {α : Type}

end less_leaky

--#check tactic.interactive.induction

meta def less_leaky.interactive.induction
:= tactic.interactive.induction'

meta def less_leaky.interactive.cases
:= tactic.interactive.cases'

meta def less_leaky.interactive.rw
:= tactic.interactive.rw'

run_cmd copy_decls

example (n : ℕ) : true :=
begin [less_leaky]
  induction n,
  trace_state,
    sorry, sorry  
end