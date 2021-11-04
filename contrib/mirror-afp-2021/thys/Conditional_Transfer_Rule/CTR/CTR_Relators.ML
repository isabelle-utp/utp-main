(* Title: CTR/CTR_Relators.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the functionality associated with the ctr relators,
including the command ctr_relator for registering the ctr relators. 
*)


signature CTR_RELATORS =
sig
structure RelatorData: GENERIC_DATA
val get_relator_data_generic : Context.generic -> RelatorData.T
val get_relator_data_proof : Proof.context -> RelatorData.T
val get_relator_data_global : theory -> RelatorData.T
val relator_of_generic : Context.generic -> Symtab.key -> term option
val relator_of_proof : Proof.context -> Symtab.key -> term option
val relator_of_global : theory -> Symtab.key -> term option
val update_relator : Symtab.key -> term -> local_theory -> local_theory
val process_ctr_relator : string -> Proof.context -> local_theory
val pr_of_typ : Proof.context -> ((string * sort) * term) list -> typ -> term
val bnf_relator_of_type_name : Proof.context -> string -> term option
end;

structure CTR_Relators : CTR_RELATORS =
struct




(**** Data ****)



(*** Data container ***)

structure RelatorData = Generic_Data
  (
    type T = term Symtab.table
    val empty = Symtab.empty
    val extend = I
    val merge = Symtab.merge (K true)
  );
 

(*** Generic operations on the relator data ***)

val get_relator_data_generic = RelatorData.get;
val get_relator_data_proof = Context.Proof #> get_relator_data_generic;
val get_relator_data_global = Context.Theory #> get_relator_data_generic;
fun relator_of_generic context = context 
  |> get_relator_data_generic 
  |> Symtab.lookup
  #> 
    (
      context 
      |> Context.theory_of 
      |> (Morphism.transfer_morphism #> Morphism.term) 
      |> Option.map
    );
val relator_of_proof = Context.Proof #> relator_of_generic;
val relator_of_global = Context.Theory #> relator_of_generic;
fun update_relator k rel = Local_Theory.declaration
  {pervasive=true, syntax=false} 
  (fn phi => (k, Morphism.term phi rel) |> Symtab.update |> RelatorData.map);




(**** User input analysis ****)

fun mk_msg_ctr_relator msg = "ctr_relator: " ^ msg;
val mk_msg_not_const = "the input must be a constant term";
val mk_msg_not_body_bool = "the body of the type of the input must be bool";
val mk_msg_not_binders_2 = 
  "the type of the input must have more than two binders";
val mk_msg_not_binders_binrelT = 
  "all of the binders associated with the type of the input" ^
  "except the last two must be the binary relation types";
val mk_msg_no_dup_binrelT = 
  "the types of the binders of the binary relations associated " ^
  "with the type of the input must have no duplicates";
val mk_msg_not_binders_binrelT_ftv_stv = 
  "the types of the binders of the binary relation types associated " ^
  "with the input type must be either free type variables or " ^
  "schematic type variables";
val mk_msg_not_type_constructor = 
  "the last two binders of the input type must be " ^
  "the results of an application of a type constructor";
val mk_msg_not_identical_type_constructors =
  "the type constructors that are associated with the last two binders " ^
  "of the input type must be identical";
val mk_msg_not_identical_input_types =
  "the sequences of the input types to the type constructors that are " ^
  "associated with the last two binders of the input type must be " ^
  "identical to the sequences of the types formed by concatenating the " ^
  "type variables associated with the left hand side and the right " ^
  "hand side of the binary relation types, respectively";



(**** Command for the registration of ctr relators ****)

fun relator_type_name_of_type T =
  let
  
    val _ = T |> body_type |> curry op= HOLogic.boolT
      orelse error (mk_msg_ctr_relator mk_msg_not_body_bool)

    val binders = binder_types T
    val n = length binders
    val _ = n |> (fn n => n > 2) 
      orelse error (mk_msg_ctr_relator mk_msg_not_binders_2)

    val (relTs, (mainT_lhs, mainT_rhs)) = binders
      |> chop (n - 2)
      ||> chop 1
      ||> apfst the_single
      ||> apsnd the_single

    val _ = relTs |> map HOLogic.is_binrelT |> List.all I
      orelse error (mk_msg_ctr_relator mk_msg_not_binders_binrelT)

    val (lhs_tvars, rhs_tvars) = relTs 
      |> map HOLogic.dest_binrelT
      |> split_list
    val tvars = lhs_tvars @ rhs_tvars

    val _ = tvars |> has_duplicates op= |> not
      orelse error (mk_msg_ctr_relator mk_msg_no_dup_binrelT)
    val _ = tvars |> map (fn T => is_TVar T orelse is_TFree T) |> List.all I
      orelse error (mk_msg_ctr_relator mk_msg_not_binders_binrelT_ftv_stv)
    val _ = is_Type mainT_lhs
      orelse error (mk_msg_ctr_relator mk_msg_not_type_constructor)
    val _ = is_Type mainT_rhs
      orelse error (mk_msg_ctr_relator mk_msg_not_type_constructor)
    
    val mainT_lhs = dest_Type mainT_lhs
    val mainT_rhs = dest_Type mainT_rhs

    val _ = op= (apply2 #1 (mainT_lhs, mainT_rhs))
      orelse error (mk_msg_ctr_relator mk_msg_not_identical_type_constructors)
    val _ = lhs_tvars = #2 mainT_lhs
      orelse error (mk_msg_ctr_relator mk_msg_not_identical_input_types)
    val _ = rhs_tvars = #2 mainT_rhs
      orelse error (mk_msg_ctr_relator mk_msg_not_identical_input_types)

  in #1 mainT_lhs end;

fun process_ctr_relator args ctxt = 
  let
    val t = Syntax.read_term ctxt args
    val _ = is_Const t orelse error (mk_msg_ctr_relator mk_msg_not_const)
    val c = relator_type_name_of_type (type_of t)
  in update_relator c t ctxt end;

val _ = Outer_Syntax.local_theory 
  \<^command_keyword>\<open>ctr_relator\<close> 
  "registration of the ctr relators"
  (Parse.const >> process_ctr_relator);




(**** ctr relators combined with the bnf relators ****)

fun bnf_relator_of_type_name ctxt c = 
  let
    fun bnf_relator_of_type_name ctxt c = 
      let 
        val relator_of_bnf = BNF_Def.rel_of_bnf 
          #> strip_comb 
          #> #1
          #> dest_Const
          #> #1
          #> Syntax.read_term ctxt
          #> Logic.varify_global
      in c |> BNF_Def.bnf_of ctxt |> Option.map relator_of_bnf end
  in
    case relator_of_proof ctxt c of
        SOME t => SOME t
      | NONE => bnf_relator_of_type_name ctxt c
  end;




(**** Conversion of a type to a parametricity relation ****)

(* 
The algorithm follows an outline of an algorithm for a similar purpose 
suggested in section 4.1 of the Ph.D. thesis of Ondřej Kunčar titled 
"Types, Abstraction and Parametric Polymorphism in Higher-Order Logic". 
*)
fun pr_of_typ ctxt ftv_spec_relt T =
  let
    fun pr_of_typ _ trel (TFree ftv_spec) = trel ftv_spec
      | pr_of_typ _ _ (Type (c, [])) = 
          Const 
            (
              \<^const_name>\<open>HOL.eq\<close>, 
              HOLogic.mk_binrelT (Type (c, []), Type (c, []))
            )
      | pr_of_typ relator_of_type_name trel (Type (c, Ts)) = 
          let
            val constt = relator_of_type_name c
              handle Option => 
                raise TYPE ("pr_of_typ: no relator", [Type (c, Ts)], []) 
            val constT = type_of constt
            val binders = constT |> binder_types |> take (length Ts)
            val argts = map (pr_of_typ relator_of_type_name trel) Ts
            val argTs = map type_of argts
            val tyenv_match = Type.typ_matches 
              (Proof_Context.tsig_of ctxt) (binders, argTs) Vartab.empty
              handle Type.TYPE_MATCH => 
                raise TYPE ("pr_of_typ: invalid relator", [Type (c, Ts)], [])
            val constt = constt
              |> dest_Const
              ||> K (Envir.subst_type tyenv_match constT)
              |> Const
          in list_comb (constt, argts) end
      | pr_of_typ _ _ T = raise TYPE ("pr_of_typ: type", single T, [])
    val trel = AList.lookup op= ftv_spec_relt #> the
  in pr_of_typ (bnf_relator_of_type_name ctxt #> the) trel T end;

end;