section \<open> UTP Schema Types \<close>

theory utp_schema
  imports "utp_definition"
  keywords "schema" :: "thy_decl_block"
begin

text \<open> Create a type with invariants attached; similar to a Z schema. \<close>

(* TODO: Inherit invariants from extended schemas, add more robust type definition. *)

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword schema} "define a new schema type"
    (Parse_Spec.overloaded -- (Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding) -- Scan.optional (@{keyword "where"} |-- Scan.repeat1 Parse.term) ["true"]
    >> (fn (((overloaded, x), (y, z)), ts) =>
        let val n = Binding.name_of (snd x)
                   val invn = n ^ "_inv"
                   val itb = Binding.make (invn ^ "_def", Position.none)               
                   val ib = (SOME (Binding.make (invn, Position.none), SOME ("('a " ^ n ^ "_scheme) upred"), NoSyn))
                 open HOLogic in
        Toplevel.theory
          (Lens_Utils.add_alphabet_cmd {overloaded = overloaded} x y z
           #> Named_Target.theory_map
              (fn ctx =>
               let val invs = Library.foldr1 HOLogic.mk_conj (map (Syntax.parse_term ctx) ts) 
               in 
                 snd (UTP_Def.utp_def (itb, []) ib (mk_eq (Free (invn, dummyT), invs)) ctx)
               end)
           #> Named_Target.theory_map 
              (fn ctx => 
               let val Const (cn, _) = Syntax.read_term ctx invn 
                       val ty = Syntax.read_typ ctx (n ^ " upred") in
               Specification.abbreviation Syntax.mode_default (SOME (Binding.make (n, Position.none), SOME ty, NoSyn)) [] (Logic.mk_equals (Free (n, dummyT), Const (cn, dummyT))) false ctx
               end)
)
        end));
\<close>

end