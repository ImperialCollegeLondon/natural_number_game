open tactic

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `kevin.interactive

@[reducible] meta def filter (d : declaration) : bool :=
d.to_name ∉ [`tactic.interactive.induction]

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive ∧ filter dec) (copy_decl dec)

@[reducible] meta def kevin := tactic

namespace kevin

--meta instance : monad kevin := by delta kevin; apply_instance

--meta instance : alternative kevin := by delta kevin; apply_instance

meta def step {α} (c : kevin α) : kevin unit := 
c >> return ()

meta def save_info (p : pos) : kevin unit := 
return ()

meta def execute (c : kevin unit) : kevin unit := 
c

--meta def trace_state {α : Type}

end kevin

--#check tactic.interactive.induction

meta def kevin.interactive.induction :
  interactive.parse interactive.cases_arg_p →
  interactive.parse interactive.types.using_ident →
  interactive.parse interactive.types.with_ident_list →
  interactive.parse (optional (lean.parser.tk "generalizing" *> lean.parser.many lean.parser.ident)) → tactic unit
:= tactic.interactive.induction

run_cmd copy_decls

--example (n : ℕ) : true :=
--begin [kevin]
--  induction n,
--    sorry, sorry  
--end