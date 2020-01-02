section \<open> Definition Command for UTP \<close>

theory utp_definition
  imports "utp_pred"
  keywords "utp_def" :: "thy_decl_block"
begin 

text \<open> A first attempt at a definition command for UTP that (1) uses the lifting parser for the
  expression on the RHS and (2) adds the definitional equation to @{thm upred_defs}. \<close>

ML \<open>
structure UTP_Def =
struct

  fun mk_utp_def_eq ctx term =
    case (Type.strip_constraints term) of
      Const (@{const_name "HOL.eq"}, b) $ c $ t => 
        @{const Trueprop} $ (Const (@{const_name "HOL.eq"}, b) $ c $ utp_lift ctx t) |
      _ => raise Match;

  val upred_defs = [[Token.make_string (Binding.name_of @{binding upred_defs}, Position.none)]];

  fun utp_def attr decl term ctx =
    Specification.definition 
      (Option.map (fn x => fst (Proof_Context.read_var x ctx)) decl) [] [] 
      ((fst attr, map (Attrib.check_src ctx) (upred_defs @ snd attr)), mk_utp_def_eq ctx term) ctx

end

val _ =
let
  open UTP_Def;
in
  Outer_Syntax.local_theory \<^command_keyword>\<open>utp_def\<close> "UTP constant definition"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, (attr, term)), _), _) =>
        (fn ctx => snd (utp_def attr decl (Syntax.parse_term ctx term) ctx))))
end
\<close>               

end