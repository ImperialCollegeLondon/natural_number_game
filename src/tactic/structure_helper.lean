import data.string.basic data.list.defs
import tactic.core

def {u v w} list.mfilter_map {m : Type u → Type v} [alternative m] [monad m] {α : Type w} {β : Type u} (f : α → m β) : list α → m (list β)
| []       := return []
| (h :: t) := do h' ← (f h >>= λ v, pure $ list.cons v []) <|> pure [],
                 t' ← list.mfilter_map t,
                 return (h' ++ t')

namespace tactic

private meta def attempt_instance_build (n : name) (ns : list name) : tactic unit :=
do sorries ← ns.mmap $ λ _, to_pexpr <$> mk_sorry,
   let s : structure_instance_info := {
       struct := some n,
       field_names := ns,
       field_values := sorries,
   },
   to_expr $ pexpr.mk_structure_instance s,
   tactic.skip

private meta def capture_failure_message (tac : tactic unit) : tactic (option string) := λ s,
match tac s with
  | result.success a s'              := result.success none s
  | result.exception (some msg) _ s' := result.success (to_string $ msg ()) s
  | result.exception none pos s'     := result.exception (some $ λ _, format!"no fail msg") pos s
end

private meta def find_explicit_constructor_args_core (n : name)
  : list name → tactic (list name)
| ns :=
do msg ← capture_failure_message $ attempt_instance_build n ns,
   do { msg ← msg,
        newn ← (msg.split_on '\'').nth 1,
        find_explicit_constructor_args_core (newn :: ns)
   } <|> return ns

meta def find_explicit_structure_args (n : name) : tactic (list name) :=
do env ← get_env,
   match env.structure_fields n with
   | none := fail format!"'{n}' not a structure!"
   | some _ := list.reverse <$> find_explicit_constructor_args_core n []
   end

meta inductive constructor_arg
| default (n : name)
| implicit
| auto (tac : tactic unit)
| opt (v : expr)

namespace constructor_arg

meta def to_tactic_format : constructor_arg → tactic format
| (default n) := pure format!"(default {n})"
| (implicit) := pure format!"(implicit)"
| (auto tac) := pure format!"(auto)"
| (opt v) := do v ← pp v, pure format!"(opt {v})"

meta instance : has_to_tactic_format constructor_arg := ⟨to_tactic_format⟩

meta def classify (n : name) : binder_info → expr → tactic constructor_arg
| binder_info.default `(opt_param %%t %%v) := return $ constructor_arg.opt v
| binder_info.default `(auto_param %%t %%tac) :=
  do tac ← eval_expr name tac,
     tac ← resolve_name tac >>= to_expr >>= eval_expr (tactic unit),
     return $ constructor_arg.auto tac
| binder_info.default e := return $ constructor_arg.default n
| _ _ := return constructor_arg.implicit

meta def dispatch (ens : list name) : constructor_arg → tactic (name × pexpr)
| (default n) :=
  if n ∈ ens then do r ← resolve_name n, return (n, r)
             else failed
| _ := failed

end constructor_arg

meta def parse_constructor_args : expr → tactic (list constructor_arg)
| (expr.pi n bi t b) :=
  do m ← mk_meta_var t,
     h ← constructor_arg.classify n bi t,
     list.cons h <$> parse_constructor_args (b.instantiate_var m)
| _ := return []

end tactic

namespace environment

meta def get_constructor_type (e : environment) (n : name) : tactic expr :=
do r ← e.get n,
   match r with
   | declaration.cnst _ _ t _ := pure t
   | _ := tactic.fail "not a constructor"
   end

end environment

namespace tactic

meta def instantiate_with_minimal (n : name) : tactic unit :=
do l ← find_explicit_structure_args n,
   let placeholders := l.map $ λ _, pexpr.mk_placeholder,
   let s : structure_instance_info := {
       struct := n,
       field_names := l,
       field_values := placeholders,
   },
   tactic.refine $ pexpr.mk_structure_instance s

meta def structure_helper : tactic unit :=
do t ← target,
   env ← get_env,
   match t with
   | expr.app (expr.const sn _) e :=
     match env.structure_fields sn with
     | some l :=
       do args ← lock_tactic_state $ do {
            tactic.fsplit,
            ty ← env.get_constructor_type (sn ++ `mk),
            args ← parse_constructor_args ty,
            ens ← find_explicit_structure_args sn,
            args.mfilter_map $ constructor_arg.dispatch ens
          },
          let s : structure_instance_info := {
            struct := sn,
            field_names := args.map prod.fst,
            field_values := args.map prod.snd,
          },
          to_expr (pexpr.mk_structure_instance s) >>= exact
     | none := fail "goal not a structure"
     end
   | _ := fail "unsupported goal"
end

run_cmd add_interactive [`structure_helper]

end tactic