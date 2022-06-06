section \<open> UTP Schema Types \<close>

theory utp_schema
  imports "utp_definition"
  keywords "schema" :: "thy_decl_block"
begin

text \<open> Create a type with invariants attached; similar to a Z schema. \<close>

(* TODO: Allow names for each invariant *)

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword schema} "define a new schema type"
    ((Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding) -- Scan.optional (@{keyword "where"} |-- (Scan.repeat1 (Scan.option (Parse.binding --| Parse.$$$ ":") |-- Parse.term))) ["true"]
    >> (fn ((x, (y, z)), ts) =>
        let (* Get the new type name *)
            val n = Binding.name_of (snd x)
            (* Produce a list of type variables *)
            val varl = fold (fn _ => fn y => "_, " ^ y) (1 upto length (fst x)) "'a"
            (* Name for the new invariant *)
            val invn = n ^ "_inv"
            val itb = Binding.make (invn ^ "_def", Position.none)               
            val upred = Lexicon.unmark_type @{type_syntax upred}
            val ib = (SOME (Binding.make (invn, Position.none), SOME ("((" ^ varl ^ ")" ^ n ^ "_scheme) " ^ upred), NoSyn))
            open HOLogic in
        Toplevel.theory
          (Lens_Utils.add_alphabet_cmd x y z
           #> Named_Target.theory_map
              (fn ctx =>
               let val invs = Library.foldr1 HOLogic.mk_conj (map (Syntax.parse_term ctx) ts)
                   val sinv = case y of
                      NONE => invs |
                      SOME t => case (Syntax.parse_typ ctx t) of
                        Type (n, _) => (case (Syntax.parse_term ctx (n ^ "_inv")) of
                          Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ Const (n', _) => HOLogic.mk_conj (Const (n', dummyT), invs) | _ => invs) |
                        _ => invs
               in 
                 snd (UTP_Def.utp_def (itb, []) ib (mk_eq (Free (invn, dummyT), sinv)) ctx)
               end)
           #> Named_Target.theory_map 
              (fn ctx => 
               let val Const (cn, _) = Syntax.read_term ctx invn 
                   val varl = 
                     if (length (fst x) = 0)
                     then ""
                     else "(" ^ foldr1 (fn (x, y) => "_, " ^ x) (map (fn _ => "_") (1 upto length (fst x))) ^ ") "
                   val ty = Syntax.read_typ ctx (varl ^ n ^ " " ^ upred) in
               Specification.abbreviation Syntax.mode_default (SOME (Binding.make (n, Position.none), SOME ty, NoSyn)) [] (Logic.mk_equals (Free (n, dummyT), Const (cn, dummyT))) false ctx
               end)
)
        end));
\<close>

end