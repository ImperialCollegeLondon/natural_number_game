-- this is how structure_helper works. I liked my name
-- better though -- `i_checked_all_teh_axioms`

namespace tactic.interactive
open tactic

meta def replace_special_names : name → name
| `add := `has_add.add
| n := n

meta def i_checked_all_teh_axioms : tactic unit :=
do t ← target,
   env ← get_env,
   match t with
   | expr.app (expr.const sn _) e :=
    match env.structure_fields sn with
    | some l :=
    do n :: _ ← tactic.open_namespaces,
       let lf := l.map replace_special_names,
       v ← lf.mmap resolve_name,
       let s : structure_instance_info := {
           struct := some sn,
           field_names := l,
           field_values := v,
       },
       e ← to_expr $ pexpr.mk_structure_instance s,
       tactic.exact e
    | none := fail "goal not a structure"
    end
   | _ := fail "unsupported goal"
   end

end tactic.interactive
