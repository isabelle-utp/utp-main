(*
(C) Copyright Andreas Viktor Hess, DTU, 2020
(C) Copyright Sebastian A. Mödersheim, DTU, 2020
(C) Copyright Achim D. Brucker, University of Exeter, 2020
(C) Copyright Anders Schlichtkrull, DTU, 2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      trac.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>Support for the Trac Format\<close>
theory
  "trac"
  imports
  trac_fp_parser
  trac_protocol_parser
keywords
      "trac" :: thy_decl
  and "trac_import" :: thy_decl
  and "trac_trac" :: thy_decl
  and "trac_import_trac" :: thy_decl
  and "protocol_model_setup" :: thy_decl
  and "protocol_security_proof" :: thy_decl
  and "manual_protocol_model_setup" :: thy_decl
  and "manual_protocol_security_proof" :: thy_decl
  and "compute_fixpoint" :: thy_decl
  and "compute_SMP" :: thy_decl
  and "setup_protocol_model'" :: thy_decl
  and "protocol_security_proof'" :: thy_decl
  and "setup_protocol_checks" :: thy_decl
begin

ML \<open>
(* Some of this is based on code from the following files distributed with Isabelle 2018:
    * HOL/Tools/value_command.ML
    * HOL/Code_Evaluation.thy
    * Pure.thy
*)

fun protocol_model_interpretation_defs name = 
  let
    fun f s =
      (Binding.empty_atts:Attrib.binding, ((Binding.name s, NoSyn), name ^ "." ^ s))
  in
    (map f [
      "public", "arity", "Ana", "\<Gamma>", "\<Gamma>\<^sub>v", "timpls_transformable_to", "intruder_synth_mod_timpls",
      "analyzed_closed_mod_timpls", "timpls_transformable_to'", "intruder_synth_mod_timpls'",
      "analyzed_closed_mod_timpls'", "admissible_transaction_terms", "admissible_transaction",
      "abs_substs_set", "abs_substs_fun", "in_trancl", "transaction_poschecks_comp",
      "transaction_negchecks_comp", "transaction_check_comp", "transaction_check",
      "transaction_check_pre", "transaction_check_post", "compute_fixpoint_fun'",
      "compute_fixpoint_fun", "attack_notin_fixpoint", "protocol_covered_by_fixpoint",
      "analyzed_fixpoint", "wellformed_protocol'", "wellformed_protocol", "wellformed_fixpoint",
      "wellformed_composable_protocols", "composable_protocols"
    ]):string Interpretation.defines
 end

fun protocol_model_interpretation_params name =
  let
    fun f s = name ^ "_" ^ s
  in
    map SOME  [f "arity", "\<lambda>_. 0", f "public", f "Ana", f "\<Gamma>", "0::nat", "1::nat"]
  end

fun declare_thm_attr attribute name print lthy =
  let 
    val arg = [(Facts.named name, [[Token.make_string (attribute, Position.none)]])]
    val (_, lthy') = Specification.theorems_cmd "" [(Binding.empty_atts, arg)] [] print lthy
  in
    lthy'
  end

fun declare_def_attr attribute name = declare_thm_attr attribute (name ^ "_def")

val declare_code_eqn = declare_def_attr "code"

val declare_protocol_check = declare_def_attr "protocol_checks"

fun declare_protocol_checks print =
  declare_protocol_check "attack_notin_fixpoint" print #>
  declare_protocol_check "protocol_covered_by_fixpoint" print #>
  declare_protocol_check "analyzed_fixpoint" print #>
  declare_protocol_check "wellformed_protocol'" print #>
  declare_protocol_check "wellformed_protocol" print #>
  declare_protocol_check "wellformed_fixpoint" print #>
  declare_protocol_check "compute_fixpoint_fun" print

fun eval_define (name, raw_t) lthy = 
  let 
    val t = Code_Evaluation.dynamic_value_strict lthy (Syntax.read_term lthy raw_t)
    val arg = ((Binding.name name, NoSyn), ((Binding.name (name ^ "_def"),[]), t))
    val (_, lthy') = Local_Theory.define arg lthy
  in
    (t, lthy')
  end

fun eval_define_declare (name, raw_t) print =
  eval_define (name, raw_t) ##> declare_code_eqn name print

val _ = Outer_Syntax.local_theory' @{command_keyword "compute_fixpoint"} 
        "evaluate and define protocol fixpoint"
        (Parse.name -- Parse.name >> (fn (protocol, fixpoint) => fn print =>
          snd o eval_define_declare (fixpoint, "compute_fixpoint_fun " ^ protocol) print));

val _ = Outer_Syntax.local_theory' @{command_keyword "compute_SMP"} 
        "evaluate and define a finite representation of the sub-message patterns of a protocol"
        ((Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "no_optimizations") --
          Parse.name -- Parse.name >> (fn ((opt,protocol), smp) => fn print =>
          let
            val rmd = "List.remdups"
            val f = "Stateful_Strands.trms_list\<^sub>s\<^sub>s\<^sub>t"
            val g =
              "(\<lambda>T. " ^ f ^ " T@map (pair' prot_fun.Pair) (Stateful_Strands.setops_list\<^sub>s\<^sub>s\<^sub>t T))"
            fun s trms =
              "(" ^ rmd ^ " (List.concat (List.map (" ^ trms ^
              " \<circ> Labeled_Strands.unlabel \<circ> transaction_strand) " ^ protocol ^ ")))"
            val opt1 = "remove_superfluous_terms \<Gamma>"
            val opt2 = "generalize_terms \<Gamma> is_Var"
            val gsmp_opt =
              "generalize_terms \<Gamma> (\<lambda>t. is_Var t \<and> t \<noteq> TAtom AttackType \<and> " ^
              "t \<noteq> TAtom SetType \<and> t \<noteq> TAtom OccursSecType \<and> \<not>is_Atom (the_Var t))"
            val smp_fun = "SMP0 Ana \<Gamma>"
            fun smp_fun' opts =
              "(\<lambda>T. let T' = (" ^ rmd ^ " \<circ> " ^ opts ^ " \<circ> " ^ smp_fun ^
              ") T in List.map (\<lambda>t. t \<cdot> Typed_Model.var_rename (Typed_Model.max_var_set " ^
              "(Messages.fv\<^sub>s\<^sub>e\<^sub>t (set (T@T'))))) T')"
            val cmd =
              if opt = "no_optimizations" then smp_fun ^ " " ^ s f
              else if opt = "optimized"
              then smp_fun' (opt1 ^ " \<circ> " ^ opt2) ^ " " ^ s f
              else if opt = "GSMP"
              then smp_fun' (opt1 ^ " \<circ> " ^ gsmp_opt) ^ " " ^ s g
              else error ("Invalid option: " ^ opt)
          in
            snd o eval_define_declare (smp, cmd) print
          end));

val _ = Outer_Syntax.local_theory' @{command_keyword "setup_protocol_checks"}
        "setup protocol checks"
        (Parse.name -- Parse.name >> (fn (protocol_model, protocol_name) => fn print =>
          let
            val a1 = "coverage_check_intro_lemmata"
            val a2 = "coverage_check_unfold_lemmata"
            val a3 = "coverage_check_unfold_protocol_lemma"
          in
            declare_protocol_checks print #>
            declare_thm_attr a1 (protocol_model ^ ".protocol_covered_by_fixpoint_intros") print #>
            declare_def_attr a2 (protocol_model ^ ".protocol_covered_by_fixpoint") print #>
            declare_def_attr a3 protocol_name print
          end
        ));

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>setup_protocol_model'\<close>
    "prove interpretation of protocol model locale into global theory"
    (Parse.!!! (Parse.name -- Parse_Spec.locale_expression) >> (fn (prefix,expr) => fn lthy =>
    let
      fun f x y z = ([(x,(y,(Expression.Positional z,[])))],[])
      val (a,(b,c)) = nth (fst expr) 0
      val name = fst b
      val _ = case c of (Expression.Named [],[]) => () | _ => error "Invalid arguments"
      val pexpr = f a b (protocol_model_interpretation_params prefix)
      val pdefs = protocol_model_interpretation_defs name
    in
      if name = ""
      then error "No name given"
      else Interpretation.global_interpretation_cmd pexpr pdefs lthy
  end));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>protocol_security_proof'\<close>
    "prove interpretation of secure protocol locale into global theory"
    (Parse.!!! (Parse.name -- Parse_Spec.locale_expression) >> (fn (prefix,expr) => fn print =>
    let
      fun f x y z = ([(x,(y,(Expression.Positional z,[])))],[])
      val (a,(b,c)) = nth (fst expr) 0
      val d = case c of (Expression.Positional ps,[]) => ps | _ => error "Invalid arguments"
      val pexpr = f a b (protocol_model_interpretation_params prefix@d)
    in
      declare_protocol_checks print #> Interpretation.global_interpretation_cmd pexpr []
    end
    ));
\<close>

ML\<open>
structure ml_isar_wrapper = struct
  fun define_constant_definition (constname, trm) lthy = 
    let
      val arg = ((Binding.name constname, NoSyn), ((Binding.name (constname^"_def"),[]), trm))
      val ((_, (_ , thm)), lthy') = Local_Theory.define arg lthy
    in
      (thm, lthy')
    end

  fun define_constant_definition' (constname, trm) print lthy = 
    let
      val arg = ((Binding.name constname, NoSyn), ((Binding.name (constname^"_def"),[]), trm))
      val ((_, (_ , thm)), lthy') = Local_Theory.define arg lthy
      val lthy'' = declare_code_eqn constname print lthy'
    in
      (thm, lthy'')
    end

  fun define_simple_abbrev (constname, trm) lthy = 
    let
      val arg = ((Binding.name constname, NoSyn), trm)
      val ((_, _), lthy') = Local_Theory.abbrev Syntax.mode_default arg lthy
    in
      lthy'
    end

  fun define_simple_type_synonym (name, typedecl) lthy = 
    let
      val (_, lthy') = Typedecl.abbrev_global (Binding.name name, [], NoSyn) typedecl lthy
    in
      lthy'
    end

  fun define_simple_datatype (dt_tyargs, dt_name) constructors =
    let
      val options = Plugin_Name.default_filter
      fun lift_c (tyargs, name) =  (((Binding.empty, Binding.name name), map (fn t => (Binding.empty, t)) tyargs), NoSyn)
      val c_spec = map lift_c constructors
      val datatyp = ((map (fn ty => (NONE, ty)) dt_tyargs, Binding.name dt_name), NoSyn) 
      val dtspec =
        ((options,false),
         [(((datatyp, c_spec), (Binding.empty, Binding.empty, Binding.empty)), [])])
    in
      BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec
    end

   fun define_simple_primrec pname precs lthy = 
     let
       val rec_eqs = map (fn (lhs,rhs) => (((Binding.empty,[]), HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))),[],[])) precs 
     in
       snd (BNF_LFP_Rec_Sugar.primrec false [] [(Binding.name pname, NONE, NoSyn)] rec_eqs lthy)
     end

   fun define_simple_fun pname precs lthy = 
     let
       val rec_eqs = map (fn (lhs,rhs) => (((Binding.empty,[]), HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))),[],[])) precs 
     in
       Function_Fun.add_fun [(Binding.name pname, NONE, NoSyn)] rec_eqs  Function_Common.default_config lthy
     end

   fun prove_simple name stmt tactic lthy = 
     let
       val thm = Goal.prove lthy [] [] stmt (fn {context, ...} => tactic context) 
                 |> Goal.norm_result lthy
                 |> Goal.check_finished lthy
     in 
       lthy |>
       snd o  Local_Theory.note ((Binding.name name, []), [thm])
     end

    fun prove_state_simple method proof_state = 
           Seq.the_result "error in proof state" ( (Proof.refine method proof_state))
               |> Proof.global_done_proof 

end
\<close>

ML\<open>

structure trac_definitorial_package = struct
  (* constant names *)
  open Trac_Utils
  val enum_constsN="enum_consts"
  val setsN="sets"
  val funN="fun"
  val atomN="atom"
  val arityN="arity"
  val publicN = "public"
  val gammaN = "\<Gamma>"
  val anaN = "Ana"
  val valN = "val"
  val timpliesN = "timplies"
  val occursN = "occurs"
  val enumN = "enum"
  val priv_fun_secN = "PrivFunSec"
  val secret_typeN = "SecretType"
  val enum_typeN = "EnumType"
  val other_pubconsts_typeN = "PubConstType"

  val types = [enum_typeN, secret_typeN]
  val special_funs = ["occurs", "zero", valN, priv_fun_secN]

  fun mk_listT T =  Type ("List.list", [T])
  val mk_setT = HOLogic.mk_setT
  val boolT = HOLogic.boolT
  val natT = HOLogic.natT
  val mk_tupleT =  HOLogic.mk_tupleT
  val mk_prodT = HOLogic.mk_prodT

  val mk_set = HOLogic.mk_set
  val mk_list = HOLogic.mk_list
  val mk_nat = HOLogic.mk_nat
  val mk_eq = HOLogic.mk_eq
  val mk_Trueprop = HOLogic.mk_Trueprop
  val mk_tuple = HOLogic.mk_tuple
  val mk_prod = HOLogic.mk_prod

  fun mkN (a,b) = a^"_"^b

  val info = Output.information

  fun rm_special_funs sel l = list_minus (list_rm_pair sel) l special_funs

  fun is_priv_fun (trac:TracProtocol.protocol) f = let
    val funs = #private (Option.valOf (#function_spec trac))
    in
      (* not (List.find (fn g => fst g = f) funs = NONE) *)
      List.exists (fn (g,n) => f = g andalso n <> "0") funs
    end

  fun full_name name lthy =
    Local_Theory.full_name lthy (Binding.name name)

  fun full_name' n (trac:TracProtocol.protocol) lthy = full_name (mkN (#name trac, n)) lthy

  fun mk_prot_type name targs (trac:TracProtocol.protocol) lthy =
    Term.Type (full_name' name trac lthy, targs)

  val enum_constsT = mk_prot_type enum_constsN []

  fun mk_enum_const a trac lthy =
    Term.Const (full_name' enum_constsN trac lthy ^ "." ^ a, enum_constsT trac lthy)

  val databaseT = mk_prot_type setsN []

  val funT = mk_prot_type funN []

  val atomT = mk_prot_type atomN []

  fun messageT (trac:TracProtocol.protocol) lthy =
    Term.Type ("Transactions.prot_term", [funT trac lthy, atomT trac lthy, databaseT trac lthy])

  fun message_funT (trac:TracProtocol.protocol) lthy =
    Term.Type ("Transactions.prot_fun", [funT trac lthy, atomT trac lthy, databaseT trac lthy])

  fun message_varT (trac:TracProtocol.protocol) lthy =
    Term.Type ("Transactions.prot_var", [funT trac lthy, atomT trac lthy, databaseT trac lthy])

  fun message_term_typeT (trc:TracProtocol.protocol) lthy =
    Term.Type ("Transactions.prot_term_type", [funT trc lthy, atomT trc lthy, databaseT trc lthy])

  fun message_atomT (trac:TracProtocol.protocol) lthy =
    Term.Type ("Transactions.prot_atom", [atomT trac lthy])

  fun messageT' varT (trac:TracProtocol.protocol) lthy =
    Term.Type ("Term.term", [message_funT trac lthy, varT])

  fun message_listT (trac:TracProtocol.protocol) lthy =
    mk_listT (messageT trac lthy)

  fun message_listT' varT (trac:TracProtocol.protocol) lthy =
    mk_listT (messageT' varT trac lthy)

  fun absT (trac:TracProtocol.protocol) lthy =
    mk_setT (databaseT trac lthy)

  fun abssT (trac:TracProtocol.protocol) lthy =
    mk_setT (absT trac lthy)

  val poscheckvariantT =
    Term.Type ("Strands_and_Constraints.poscheckvariant", [])

  val strand_labelT =
    Term.Type ("Labeled_Strands.strand_label", [natT])

  fun strand_stepT (trac:TracProtocol.protocol) lthy =
    Term.Type ("Stateful_Strands.stateful_strand_step",
               [message_funT trac lthy, message_varT trac lthy])

  fun labeled_strand_stepT (trac:TracProtocol.protocol) lthy =
    mk_prodT (strand_labelT, strand_stepT trac lthy)

  fun prot_strandT (trac:TracProtocol.protocol) lthy =
    mk_listT (labeled_strand_stepT trac lthy)

  fun prot_transactionT (trac:TracProtocol.protocol) lthy =
    Term.Type ("Transactions.prot_transaction",
               [funT trac lthy, atomT trac lthy, databaseT trac lthy, natT])

  val mk_star_label =
    Term.Const ("Labeled_Strands.strand_label.LabelS", strand_labelT)

  fun mk_prot_label (lbl:int) =
    Term.Const ("Labeled_Strands.strand_label.LabelN", natT --> strand_labelT) $
      mk_nat lbl

  fun mk_labeled_step (label:term) (step:term) =
    mk_prod (label, step)

  fun mk_Send_step (trac:TracProtocol.protocol) lthy (label:term) (msg:term) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Send",
                   messageT trac lthy --> strand_stepT trac lthy) $ msg)

  fun mk_Receive_step (trac:TracProtocol.protocol) lthy (label:term) (msg:term) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Receive",
                   messageT trac lthy --> strand_stepT trac lthy) $ msg)

  fun mk_InSet_step (trac:TracProtocol.protocol) lthy (label:term) (elem:term) (set:term) =
    let
      val psT = [poscheckvariantT, messageT trac lthy, messageT trac lthy]
    in
      mk_labeled_step label
        (Term.Const ("Stateful_Strands.stateful_strand_step.InSet",
                     psT ---> strand_stepT trac lthy) $
         Term.Const ("Strands_and_Constraints.poscheckvariant.Check", poscheckvariantT) $
         elem $ set)
    end

  fun mk_NotInSet_step (trac:TracProtocol.protocol) lthy (label:term) (elem:term) (set:term) =
    let
      val varT = message_varT trac lthy
      val trm_prodT = mk_prodT (messageT trac lthy, messageT trac lthy)
      val psT = [mk_listT varT, mk_listT trm_prodT, mk_listT trm_prodT]
    in
      mk_labeled_step label
        (Term.Const ("Stateful_Strands.stateful_strand_step.NegChecks",
                     psT ---> strand_stepT trac lthy) $
         mk_list varT [] $
         mk_list trm_prodT [] $
         mk_list trm_prodT [mk_prod (elem,set)])
    end

  fun mk_Inequality_step (trac:TracProtocol.protocol) lthy (label:term) (t1:term) (t2:term) =
    let
      val varT = message_varT trac lthy
      val trm_prodT = mk_prodT (messageT trac lthy, messageT trac lthy)
      val psT = [mk_listT varT, mk_listT trm_prodT, mk_listT trm_prodT]
    in
      mk_labeled_step label
        (Term.Const ("Stateful_Strands.stateful_strand_step.NegChecks",
                     psT ---> strand_stepT trac lthy) $
         mk_list varT [] $
         mk_list trm_prodT [mk_prod (t1,t2)] $
         mk_list trm_prodT [])
    end

  fun mk_Insert_step (trac:TracProtocol.protocol) lthy (label:term) (elem:term) (set:term) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Insert",
                   [messageT trac lthy, messageT trac lthy] ---> strand_stepT trac lthy) $
       elem $ set)

  fun mk_Delete_step (trac:TracProtocol.protocol) lthy (label:term) (elem:term) (set:term) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Delete",
                   [messageT trac lthy, messageT trac lthy] ---> strand_stepT trac lthy) $
       elem $ set)

  fun mk_Transaction (trac:TracProtocol.protocol) lthy S1 S2 S3 S4 S5 S6 =
    let
      val varT = message_varT trac lthy
      val msgT = messageT trac lthy
      val var_listT = mk_listT varT
      val msg_listT = mk_listT msgT
      val trT = prot_transactionT trac lthy
      (* val decl_elemT = mk_prodT (varT, mk_listT msgT)
      val declT = mk_listT decl_elemT *)
      val stepT = labeled_strand_stepT trac lthy
      val strandT = prot_strandT trac lthy
      val strandsT = mk_listT strandT
      val paramsT = [(* declT,  *)var_listT, strandT, strandT, strandT, strandT, strandT]
    in
      Term.Const ("Transactions.prot_transaction.Transaction", paramsT ---> trT) $
      (* mk_list decl_elemT [] $ *)
      (if null S4 then mk_list varT []
       else (Term.Const (@{const_name "map"}, [msgT --> varT, msg_listT] ---> var_listT) $
             Term.Const (@{const_name "the_Var"}, msgT --> varT) $
             mk_list msgT S4)) $
      mk_list stepT S1 $
      mk_list stepT [] $
      (if null S3 then mk_list stepT S2
       else (Term.Const (@{const_name "append"}, [strandT,strandT] ---> strandT) $
             mk_list stepT S2 $
            (Term.Const (@{const_name "concat"}, strandsT --> strandT) $ mk_list strandT S3))) $
      mk_list stepT S5 $
      mk_list stepT S6
    end

  fun get_funs (trac:TracProtocol.protocol) =
      let
        fun append_sec fs = fs@[(priv_fun_secN, "0")]
        val filter_funs = filter (fn (_,n) => n <> "0")
        val filter_consts = filter (fn (_,n) => n = "0")
        fun inc_ar (s,n) = (s, Int.toString (1+Option.valOf (Int.fromString n)))
      in
        case (#function_spec trac) of 
             NONE => ([],[],[])
           | SOME ({public=pub, private=priv}) =>
              let
                val pub_symbols = rm_special_funs fst (pub@map inc_ar (filter_funs priv))
                val pub_funs = filter_funs pub_symbols
                val pub_consts = filter_consts pub_symbols
                val priv_consts = append_sec (rm_special_funs fst (filter_consts priv))
              in
                (pub_funs, pub_consts, priv_consts)
              end
      end 

  fun get_set_spec (trac:TracProtocol.protocol) =
    mk_unique (map (fn (s,n) => (s,Option.valOf (Int.fromString n))) (#set_spec trac))

  fun set_arity (trac:TracProtocol.protocol) s =
    case List.find (fn x => fst x = s) (get_set_spec trac) of
      SOME (_,n) => SOME n
    | NONE => NONE

  fun get_enums (trac:TracProtocol.protocol) =
    mk_unique (TracProtocol.extract_Consts (#type_spec trac))

  fun flatten_type_spec (trac:TracProtocol.protocol) =
    let
      fun find_type taus tau =
        case List.find (fn x => fst x = tau) taus of
          SOME x => snd x
        | NONE => error ("Type " ^ tau ^ " has not been declared")
      fun step taus (s,e) =
        case e of
          TracProtocol.Union ts =>
            let
              val es = map (find_type taus) ts
              fun f es' = mk_unique (List.concat (map TracProtocol.the_Consts es'))
            in
              if List.all TracProtocol.is_Consts es
              then (s,TracProtocol.Consts (f es))
              else (s,TracProtocol.Union ts)
            end
        | c => (s,c)
      fun loop taus =
        let
          val taus' = map (step taus) taus
        in
          if taus = taus'
          then taus
          else loop taus'
        end
      val flat_type_spec =
        let
          val x = loop (#type_spec trac)
          val errpre = "Couldn't flatten the enumeration types: "
        in
          if List.all (fn (_,e) => TracProtocol.is_Consts e) x
          then
            let
              val y = map (fn (s,e) => (s,TracProtocol.the_Consts e)) x
            in
              if List.all (not o List.null o snd) y
              then y
              else error (errpre ^ "does every type have at least one value?")
            end
          else error (errpre ^ "have all types been declared?")
        end
    in
      flat_type_spec
    end

  fun is_attack_transaction (tr:TracProtocol.cTransaction) =
    not (null (#attack_actions tr))

  fun get_transaction_name (tr:TracProtocol.cTransaction) =
    #1 (#transaction tr)

  fun get_fresh_value_variables (tr:TracProtocol.cTransaction) =
    map_filter (TracProtocol.maybe_the_Fresh o snd) (#fresh_actions tr)

  fun get_nonfresh_value_variables (tr:TracProtocol.cTransaction) =
    map fst (filter (fn x => snd x = "value") (#2 (#transaction tr)))

  fun get_value_variables (tr:TracProtocol.cTransaction) =
    get_nonfresh_value_variables tr@get_fresh_value_variables tr

  fun get_enum_variables (tr:TracProtocol.cTransaction) =
    mk_unique (filter (fn x => snd x <> "value") (#2 (#transaction tr)))

  fun get_variable_restrictions (tr:TracProtocol.cTransaction) =
    let
      val enum_vars = get_enum_variables tr
      val value_vars = get_value_variables tr
      fun enum_member x = List.exists (fn y => x = fst y)
      fun value_member x = List.exists (fn y => x = y)
      fun aux [] = ([],[])
        | aux ((a,b)::rs) =
            if enum_member a enum_vars andalso enum_member b enum_vars
            then let val (es,vs) = aux rs in ((a,b)::es,vs) end
            else if value_member a value_vars andalso value_member b value_vars
            then let val (es,vs) = aux rs in (es,(a,b)::vs) end
            else error ("Ill-formed or ill-typed variable restriction: " ^ a ^ " != " ^ b)
    in
      aux (#3 (#transaction tr))
    end

  fun conv_enum_consts trac (t:Trac_Term.cMsg) = 
    let
      open Trac_Term
      val enums = get_enums trac
      fun aux (cFun (f,ts)) =
            if List.exists (fn x => x = f) enums
            then if null ts
                 then cEnum f
                 else error ("Enum constant " ^ f ^ " should not have a parameter list")
            else
              cFun (f,map aux ts)
        | aux (cConst c) =
            if List.exists (fn x => x = c) enums
            then cEnum c
            else cConst c
        | aux (cSet (s,ts)) = cSet (s,map aux ts)
        | aux (cOccursFact bs) = cOccursFact (aux bs)
        | aux t = t
    in
      aux t
    end

  fun val_to_abs_list vs =
    let
      open Trac_Term
      fun aux t = case t of cEnum b => b | _ => error "Invalid val parameter list"
    in
      case vs of
        [] => []
      | (cConst "0"::ts) => val_to_abs_list ts
      | (cFun (s,ps)::ts) => (s, map aux ps)::val_to_abs_list ts
      | (cSet (s,ps)::ts) => (s, map aux ps)::val_to_abs_list ts
      | _ => error "Invalid val parameter list"
    end

  fun val_to_abs (t:Trac_Term.cMsg) =
    let
      open Trac_Term
      fun aux t = case t of cEnum b => b | _ => error "Invalid val parameter list"

      fun val_to_abs_list [] = []
      | val_to_abs_list (cConst "0"::ts) = val_to_abs_list ts
      | val_to_abs_list (cFun (s,ps)::ts) = (s, map aux ps)::val_to_abs_list ts
      | val_to_abs_list (cSet (s,ps)::ts) = (s, map aux ps)::val_to_abs_list ts
      | val_to_abs_list _ = error "Invalid val parameter list"
    in
      case t of
        cFun (f,ts) =>
          if f = valN
          then cAbs (val_to_abs_list ts)
          else cFun (f,map val_to_abs ts)
      | cSet (s,ts) =>
          cSet (s,map val_to_abs ts)
      | cOccursFact bs =>
          cOccursFact (val_to_abs bs)
      | t => t
    end

  fun occurs_enc t =
    let
      open Trac_Term
      fun aux [cVar x] = cVar x
        | aux [cAbs bs] = cAbs bs
        | aux _ = error "Invalid occurs parameter list"
      fun enc (cFun (f,ts)) = (
            if f = occursN
            then cOccursFact (aux ts)
            else cFun (f,map enc ts))
        | enc (cSet (s,ts)) =
            cSet (s,map enc ts)
        | enc (cOccursFact bs) =
            cOccursFact (enc bs)
        | enc t = t
    in
      enc t
    end

  fun priv_fun_enc trac (Trac_Term.cFun (f,ts)) = (
        if is_priv_fun trac f andalso
           (case ts of Trac_Term.cPrivFunSec::_ => false | _ => true)
        then Trac_Term.cFun (f,Trac_Term.cPrivFunSec::map (priv_fun_enc trac) ts)
        else Trac_Term.cFun (f,map (priv_fun_enc trac) ts))
    | priv_fun_enc _ t = t

  fun transform_cMsg trac =
    priv_fun_enc trac o occurs_enc o val_to_abs o conv_enum_consts trac

  fun check_no_vars_and_consts (fp:Trac_Term.cMsg list) =
    let
      open Trac_Term
      fun aux (cVar _) = false
        | aux (cConst _) = false
        | aux (cFun (_,ts)) = List.all aux ts
        | aux (cSet (_,ts)) = List.all aux ts
        | aux (cOccursFact bs) = aux bs
        | aux _ = true
    in
      if List.all aux fp
      then fp
      else error "There shouldn't be any cVars and cConsts at this point in the fixpoint translation"
    end

  fun split_fp (fp:Trac_Term.cMsg list) =
    let
      open Trac_Term
      fun fa t = case t of cFun (s,_) => s <> timpliesN | _ => true
      fun fb (t,ts) = case t of cOccursFact (cAbs bs) => bs::ts | _ => ts
      fun fc (cFun (s, [cAbs bs, cAbs cs]),ts) =
          if s = timpliesN
          then (bs,cs)::ts
          else ts
        | fc (_,ts) = ts

      val eq = eq_set (fn ((s,xs),(t,ys)) => s = t andalso eq_set (op =) (xs,ys))
      fun eq_pairs ((a,b),(c,d)) = eq (a,c) andalso eq (b,d)

      val timplies_trancl =
        let
          fun trans_step ts =
            let
              fun aux (s,t) = map (fn (_,u) => (s,u)) (filter (fn (v,_) => eq (t,v)) ts)
            in
              distinct eq_pairs (filter (not o eq) (ts@List.concat (map aux ts)))
            end
          fun loop ts =
            let
              val ts' = trans_step ts
            in
              if eq_set eq_pairs (ts,ts')
              then ts
              else loop ts'
            end
        in
          loop
        end

      val ti = List.foldl fc [] fp
    in
      (filter fa fp, distinct eq (List.foldl fb [] fp@map snd ti), timplies_trancl ti)
    end

  fun mk_enum_substs trac (vars:(string * Trac_Term.VarType) list) =
    let
      open Trac_Term
      val flat_type_spec = flatten_type_spec trac
      val deltas =
        let
          fun f (s,EnumType tau) = (
              case List.find (fn x => fst x = tau) flat_type_spec of
                SOME x => map (fn c => (s,c)) (snd x)
              | NONE => error ("Type " ^ tau ^ " was not found in the type specification"))
            | f (s,_) = error ("Variable " ^ s ^ " is not of enum type")
        in
          list_product (map f vars)
        end
    in
      map (fn d => map (fn (x,t) => (x,cEnum t)) d) deltas
    end

  fun ground_enum_variables trac (fp:Trac_Term.cMsg list) =
    let
      open Trac_Term
      fun do_grounding t = map (fn d => subst_apply d t) (mk_enum_substs trac (fv_cMsg t))
    in
      List.concat (map do_grounding fp)
    end

  fun transform_fp trac (fp:Trac_Term.cMsg list) =
    fp |> ground_enum_variables trac
       |> map (transform_cMsg trac)
       |> check_no_vars_and_consts
       |> split_fp

  fun database_to_hol (db:string * Trac_Term.cMsg list) (trac:TracProtocol.protocol) lthy =
    let
      open Trac_Term
      val errmsg = "Invalid database parameter"
      fun mkN' n = mkN (#name trac, n)
      val s_prefix = full_name (mkN' setsN) lthy ^ "."
      val e_prefix = full_name (mkN' enum_constsN) lthy ^ "."
      val (s,es) = db
      val tau = enum_constsT trac lthy
      val databaseT = databaseT trac lthy
      val a = Term.Const (s_prefix ^ s, map (fn _ => tau) es ---> databaseT)
      fun param_to_hol (cVar (x,EnumType _)) = Term.Free (x, tau)
        | param_to_hol (cVar (x,Untyped)) = Term.Free (x, tau)
        | param_to_hol (cEnum e) = Term.Const (e_prefix ^ e, tau)
        | param_to_hol (cConst c) = error (errmsg ^ ": cConst " ^ c)
        | param_to_hol (cVar (x,ValueType)) = error (errmsg ^ ": cVar (" ^ x ^ ",ValueType)")
        | param_to_hol _ = error errmsg
    in
      fold (fn e => fn b => b $ param_to_hol e) es a
    end

  fun abs_to_hol (bs:(string * string list) list) (trac:TracProtocol.protocol) lthy =
    let
      val databaseT = databaseT trac lthy
      fun db_params_to_cEnum (a,cs) = (a, map Trac_Term.cEnum cs)
    in
      mk_set databaseT (map (fn db => database_to_hol (db_params_to_cEnum db) trac lthy) bs)
    end

  fun cMsg_to_hol (t:Trac_Term.cMsg) lbl varT var_map free_enum_var trac lthy =
    let
      open Trac_Term
      val tT = messageT' varT trac lthy
      val fT = message_funT trac lthy
      val enum_constsT = enum_constsT trac lthy
      val tsT = message_listT' varT trac lthy
      val VarT = varT --> tT
      val FunT = [fT, tsT] ---> tT
      val absT = absT trac lthy
      val databaseT = databaseT trac lthy
      val AbsT = absT --> fT
      val funT = funT trac lthy
      val FuT = funT --> fT
      val SetT = databaseT --> fT
      val enumT = enum_constsT --> funT
      val VarC = Term.Const (@{const_name "Var"}, VarT)
      val FunC = Term.Const (@{const_name "Fun"}, FunT)
      val NilC = Term.Const (@{const_name "Nil"}, tsT)
      val prot_label = mk_nat lbl
      fun full_name'' n = full_name' n trac lthy
      fun mk_enum_const' a = mk_enum_const a trac lthy
      fun mk_prot_fun_trm f tau = Term.Const ("Transactions.prot_fun." ^ f, tau)
      fun mk_enum_trm etrm =
            mk_prot_fun_trm "Fu" FuT $ (Term.Const (full_name'' funN ^ "." ^ enumN, enumT) $ etrm)
      fun mk_Fu_trm f =
            mk_prot_fun_trm "Fu" FuT $ Term.Const (full_name'' funN ^ "." ^ f, funT)
      fun c_to_h s = cMsg_to_hol s lbl varT var_map free_enum_var trac lthy
      fun c_list_to_h ts = mk_list tT (map c_to_h ts)
    in
      case t of
        cVar x =>
          if free_enum_var x
          then FunC $ mk_enum_trm (Term.Free (fst x, enum_constsT)) $ NilC
          else VarC $ var_map x
      | cConst f =>
          FunC $
          mk_Fu_trm f $
          NilC
      | cFun (f,ts) =>
          FunC $
          mk_Fu_trm f $
          c_list_to_h ts
      | cSet (s,ts) =>
          FunC $
          (mk_prot_fun_trm "Set" SetT $ database_to_hol (s,ts) trac lthy) $
          NilC
      | cAttack =>
          FunC $
          (mk_prot_fun_trm "Attack" (natT --> fT) $ prot_label) $
          NilC
      | cAbs bs =>
          FunC $
          (mk_prot_fun_trm "Abs" AbsT $ abs_to_hol bs trac lthy) $
          NilC
      | cOccursFact bs =>
          FunC $
          mk_prot_fun_trm "OccursFact" fT $
          mk_list tT [
            FunC $ mk_prot_fun_trm "OccursSec" fT $ NilC,
            c_to_h bs]
      | cPrivFunSec =>
          FunC $
          mk_Fu_trm priv_fun_secN $
          NilC
      | cEnum a =>
          FunC $
          mk_enum_trm (mk_enum_const' a) $
          NilC
  end

  fun ground_cMsg_to_hol t lbl trac lthy =
    cMsg_to_hol t lbl (message_varT trac lthy) (fn _ => error "Term not ground")
                (fn _ => false) trac lthy

  fun ana_cMsg_to_hol inc_vars t (ana_var_map:string list) =
    let
      open Trac_Term
      fun var_map (x,Untyped) = (
            case list_find (fn y => x = y) ana_var_map of
              SOME (_,n) => if inc_vars then mk_nat (1+n) else mk_nat n
            | NONE => error ("Analysis variable " ^ x ^ " not found"))
        | var_map _ = error "Analysis variables must be untyped"
      val lbl = 0 (* There's no constants in analysis messages requiring labels anyway *)
    in
      cMsg_to_hol t lbl natT var_map (fn _ => false)
    end

  fun transaction_cMsg_to_hol t lbl (transaction_var_map:string list) trac lthy =
    let
      open Trac_Term
      val varT = message_varT trac lthy
      val atomT = message_atomT trac lthy
      val term_typeT = message_term_typeT trac lthy
      fun TAtom_Value_var n =
        let
          val a = Term.Const (@{const_name "Var"}, atomT --> term_typeT) $
                  Term.Const ("Transactions.prot_atom.Value", atomT)
        in
          HOLogic.mk_prod (a, mk_nat n)
        end

      fun var_map_err_prefix x =
        "Transaction variable " ^ x ^ " should be value typed but is actually "

      fun var_map (x,ValueType) = (
            case list_find (fn y => x = y) transaction_var_map of
              SOME (_,n) => TAtom_Value_var n
            | NONE => error ("Transaction variable " ^ x ^ " not found"))
        | var_map (x,EnumType e) = error (var_map_err_prefix x ^ "of enum type " ^ e)
        | var_map (x,Untyped) = error (var_map_err_prefix x ^ "untyped")
    in
      cMsg_to_hol t lbl varT var_map (fn (_,t) => case t of EnumType _ => true | _ => false)
                  trac lthy
    end

  fun fp_triple_to_hol (fp,occ,ti) trac lthy =
    let
      val prot_label = 0
      val tau_abs = absT trac lthy
      val tau_fp_elem = messageT trac lthy
      val tau_occ_elem = tau_abs
      val tau_ti_elem = mk_prodT (tau_abs, tau_abs)
      fun a_to_h bs = abs_to_hol bs trac lthy
      fun c_to_h t = ground_cMsg_to_hol t prot_label trac lthy
      val fp' = mk_list tau_fp_elem (map c_to_h fp)
      val occ' = mk_list tau_occ_elem (map a_to_h occ)
      val ti' = mk_list tau_ti_elem (map (mk_prod o map_prod a_to_h) ti)
    in
      mk_tuple [fp', occ', ti']
    end

  fun abstract_over_enum_vars enum_vars enum_ineqs trm flat_type_spec trac lthy =
    let
      val enum_constsT = enum_constsT trac lthy
      fun enumlistelemT n = mk_tupleT (replicate n enum_constsT)
      fun enumlistT n = mk_listT (enumlistelemT n)
      fun mk_enum_const' a = mk_enum_const a trac lthy

      fun absfreeprod xs trm =
        let
          val tau = enum_constsT
          val tau_out = Term.fastype_of trm
          fun absfree' x = absfree (x,enum_constsT)
          fun aux _ [] = trm
            | aux _ [x] = absfree' x trm
            | aux len (x::y::xs) =
                Term.Const (@{const_name "case_prod"},
                       [[tau,mk_tupleT (replicate (len-1) tau)] ---> tau_out,
                        mk_tupleT (replicate len tau)] ---> tau_out) $
                absfree' x (aux (len-1) (y::xs))
        in
          aux (length xs) xs
        end

      fun mk_enum_neq (a,b) = (HOLogic.mk_not o HOLogic.mk_eq)
        (Term.Free (a, enum_constsT), Term.Free (b, enum_constsT))

      fun mk_enum_neqs_list [] = Term.Const (@{const_name "True"}, HOLogic.boolT)
        | mk_enum_neqs_list [x] = mk_enum_neq x
        | mk_enum_neqs_list (x::y::xs) = HOLogic.mk_conj (mk_enum_neq x, mk_enum_neqs_list (y::xs))

      val enum_types =
        let
          fun aux t =
            if t = ""
            then get_enums trac
            else case List.find (fn (s,_) => t = s) flat_type_spec of
                SOME (_,cs) => cs
              | NONE => error ("Not an enum type: " ^ t ^ "?")
        in
          map (aux o snd) enum_vars
        end

      val enumlist_product =
        let
          fun mk_enumlist ns = mk_list enum_constsT (map mk_enum_const' ns)

          fun aux _ [] = mk_enumlist []
            | aux _ [ns] = mk_enumlist ns
            | aux len (ns::ms::elists) =
                Term.Const ("List.product", [enumlistT 1, enumlistT (len-1)] ---> enumlistT len) $
                mk_enumlist ns $ aux (len-1) (ms::elists)
        in
          aux (length enum_types) enum_types
        end

      val absfp = absfreeprod (map fst enum_vars) trm
      val eptrm = enumlist_product
      val typof = Term.fastype_of
      val evseT = enumlistelemT (length enum_vars)
      val evslT = enumlistT (length enum_vars)
      val eneqs = absfreeprod (map fst enum_vars) (mk_enum_neqs_list enum_ineqs)
    in
      if null enum_vars
      then mk_list (typof trm) [trm]
      else if null enum_ineqs
      then Term.Const(@{const_name "map"},
                      [typof absfp, typof eptrm] ---> mk_listT (typof trm)) $
           absfp $ eptrm
      else Term.Const(@{const_name "map"},
                      [typof absfp, typof eptrm] ---> mk_listT (typof trm)) $
           absfp $ (Term.Const(@{const_name "filter"},
                               [evseT --> HOLogic.boolT, evslT] ---> evslT) $
                    eneqs $ eptrm)
    end

  fun mk_type_of_name lthy pname name ty_args
      = Type(Local_Theory.full_name lthy (Binding.name (mkN(pname, name))), ty_args)

  fun mk_mt_list t = Term.Const (@{const_name "Nil"}, mk_listT t)

  fun name_of_typ (Type (s, _)) = s
    | name_of_typ (TFree _)     = error "name_of_type: unexpected TFree"
    | name_of_typ (TVar _ )     = error "name_of_type: unexpected TVAR"

  fun prove_UNIV name typ elems thmsN lthy =
    let 
      val rhs = mk_set typ elems
      val lhs = Const("Set.UNIV",mk_setT typ)
      val stmt = mk_Trueprop (mk_eq (lhs,rhs))
      val fq_tname = name_of_typ typ 
                          
      fun inst_and_prove_enum thy = 
        let
          val _ = writeln("Inst enum: "^name)
          val lthy = Class.instantiation ([fq_tname], [], @{sort enum}) thy
          val enum_eq = Const("Pure.eq",mk_listT typ --> mk_listT typ --> propT)
                             $Const(@{const_name "enum_class.enum"},mk_listT typ)
                             $(mk_list typ elems)

          val ((_, (_, enum_def')), lthy) = Specification.definition NONE [] [] 
                                                ((Binding.name ("enum_"^name),[]), enum_eq) lthy
          val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
          val enum_def = singleton (Proof_Context.export lthy ctxt_thy) enum_def'

          val enum_all_eq = Const("Pure.eq", boolT --> boolT --> propT)
                             $(Const(@{const_name "enum_class.enum_all"},(typ --> boolT) --> boolT)
                                                  $Free("P",typ --> boolT))
                             $(Const(@{const_name "list_all"},(typ --> boolT) --> (mk_listT typ) --> boolT)
                                    $Free("P",typ --> boolT)$(mk_list typ elems))
          val ((_, (_, enum_all_def')), lthy) = Specification.definition NONE [] [] 
                                                ((Binding.name ("enum_all_"^name),[]), enum_all_eq) lthy
          val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
          val enum_all_def = singleton (Proof_Context.export lthy ctxt_thy) enum_all_def'

          val enum_ex_eq = Const("Pure.eq", boolT --> boolT --> propT)
                             $(Const(@{const_name "enum_class.enum_ex"},(typ --> boolT) --> boolT)
                                                  $Free("P",typ --> boolT))
                             $(Const(@{const_name "list_ex"},(typ --> boolT) --> (mk_listT typ) --> boolT)
                                    $Free("P",typ --> boolT)$(mk_list typ elems))
          val ((_, (_, enum_ex_def')), lthy) = Specification.definition NONE [] [] 
                                                ((Binding.name ("enum_ex_"^name),[]), enum_ex_eq) lthy
          val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
          val enum_ex_def = singleton (Proof_Context.export lthy ctxt_thy) enum_ex_def'
        in
          Class.prove_instantiation_exit (fn ctxt => 
            (Class.intro_classes_tac ctxt [])  THEN
               ALLGOALS (simp_tac (ctxt addsimps  [Proof_Context.get_thm ctxt (name^"_UNIV"),  
                                                           enum_def, enum_all_def, enum_ex_def]) ) 
            )lthy
        end
      fun inst_and_prove_finite thy = 
        let
          val lthy = Class.instantiation ([fq_tname], [], @{sort finite}) thy
        in 
          Class.prove_instantiation_exit (fn ctxt => 
            (Class.intro_classes_tac ctxt []) THEN 
             (simp_tac (ctxt addsimps[Proof_Context.get_thm ctxt (name^"_UNIV")])) 1) lthy
        end
    in 
      lthy
      |> ml_isar_wrapper.prove_simple (name^"_UNIV") stmt 
         (fn c =>     (safe_tac c) 
                 THEN (ALLGOALS(simp_tac c))
                 THEN (ALLGOALS(Metis_Tactic.metis_tac ["full_types"] 
                                   "combs"  c 
                                   (map (Proof_Context.get_thm c) thmsN)))
         )
      |> Local_Theory.raw_theory inst_and_prove_finite 
      |> Local_Theory.raw_theory inst_and_prove_enum  
    end

  fun def_types (trac:TracProtocol.protocol) lthy = 
    let 
      val pname = #name trac
      val defname = mkN(pname, enum_constsN)
      val _ = info("  Defining "^defname)
      val tnames = get_enums trac
      val types = map (fn x => ([],x)) tnames
    in 
      ([defname], ml_isar_wrapper.define_simple_datatype ([], defname) types lthy)
    end

  fun def_sets (trac:TracProtocol.protocol) lthy = 
    let 
      val pname = #name trac
      val defname = mkN(pname, setsN)
      val _ = info ("  Defining "^defname)

      val sspec = get_set_spec trac
      val tfqn = Local_Theory.full_name lthy (Binding.name (mkN(pname, enum_constsN)))
      val ttyp = Type(tfqn, [])
      val types = map (fn (x,n) => (replicate n ttyp,x)) sspec
    in
      lthy
      |> ml_isar_wrapper.define_simple_datatype ([], defname) types
    end

  fun def_funs (trac:TracProtocol.protocol) lthy = 
    let 
      val pname = #name trac
      val (pub_f, pub_c, priv) = get_funs trac
      val pub = pub_f@pub_c

      fun def_atom lthy = 
        let 
          val def_atomname = mkN(pname, atomN) 
          val types =
            if null pub_c
            then types
            else types@[other_pubconsts_typeN]
          fun define_atom_dt lthy = 
            let
              val _ = info("  Defining "^def_atomname)
            in
              lthy
              |> ml_isar_wrapper.define_simple_datatype ([], def_atomname) (map (fn x => ([],x)) types)
            end
          fun prove_UNIV_atom lthy =
            let
              val _ = info ("    Proving "^def_atomname^"_UNIV")
              val thmsN = [def_atomname^".exhaust"]
              val fqn = Local_Theory.full_name lthy (Binding.name (mkN(pname, atomN)))
              val typ = Type(fqn, [])  
            in
              lthy 
              |> prove_UNIV (def_atomname) typ (map (fn c => Const(fqn^"."^c,typ)) types) thmsN 
            end 
        in 
           lthy
           |> define_atom_dt
           |> prove_UNIV_atom
        end

      fun def_fun_dt lthy = 
        let
          val def_funname = mkN(pname, funN)
          val _ = info("  Defining "^def_funname) 
          val types = map (fn x => ([],x)) (map fst (pub@priv))
          val ctyp = Type(Local_Theory.full_name lthy (Binding.name (mkN(pname, enum_constsN))), [])
        in
          ml_isar_wrapper.define_simple_datatype ([], def_funname) (types@[([ctyp],enumN)]) lthy
        end

      fun def_fun_arity lthy = 
        let 
          val fqn_name = Local_Theory.full_name lthy (Binding.name (mkN(pname, funN)))
          val ctyp = Type(fqn_name, [])

          fun mk_rec_eq name (fname,arity) = (Free(name,ctyp --> natT)
                                               $Const(fqn_name^"."^fname,ctyp),
                                                mk_nat((Option.valOf o Int.fromString) arity))
          val name = mkN(pname, arityN)
          val _ = info("  Defining "^name) 
          val ctyp' = Type(Local_Theory.full_name lthy (Binding.name (mkN(pname, enum_constsN))), [])
        in
          ml_isar_wrapper.define_simple_fun name
              ((map (mk_rec_eq name) (pub@priv))@[
                      (Free(name, ctyp --> natT)
                           $(Const(fqn_name^"."^enumN, ctyp' --> ctyp)$(Term.dummy_pattern ctyp')),
                             mk_nat(0))]) lthy
        end

      fun def_public lthy = 
        let 
          val fqn_name = Local_Theory.full_name lthy (Binding.name (mkN(pname, funN)))
          val ctyp = Type(fqn_name, [])

          fun mk_rec_eq name t fname = (Free(name, ctyp --> boolT)
                                               $Const(fqn_name^"."^fname,ctyp), t)
          val name = mkN(pname, publicN)
          val _ = info("  Defining "^name) 
          val ctyp' = Type(Local_Theory.full_name lthy (Binding.name (mkN(pname, enum_constsN))), [])
        in
          ml_isar_wrapper.define_simple_fun name
              ((map (mk_rec_eq name (@{term "False"})) (map fst priv))
              @(map (mk_rec_eq name (@{term "True"})) (map fst pub))
              @[(Free(name, ctyp --> boolT)
                          $(Const(fqn_name^"."^enumN, ctyp' --> ctyp)$(Term.dummy_pattern ctyp')),
                             @{term "True"})]) lthy
        end

      fun def_gamma lthy = 
        let 
          fun optionT t = Type (@{type_name "option"}, [t])
          fun mk_Some t = Const (@{const_name "Some"}, t --> optionT t)
          fun mk_None t = Const (@{const_name "None"},  optionT t)

          val fqn_name = Local_Theory.full_name lthy (Binding.name (mkN(pname, funN)))
          val ctyp = Type(fqn_name, [])
          val atomFQN = Local_Theory.full_name lthy (Binding.name (mkN(pname, atomN)))
          val atomT = Type(atomFQN, [])

          fun mk_rec_eq name t fname = (Free(name, ctyp --> optionT atomT)
                                               $Const(fqn_name^"."^fname,ctyp), t)
          val name = mkN(pname, gammaN)
          val _ = info("  Defining "^name) 
          val ctyp' = Type(Local_Theory.full_name lthy (Binding.name (mkN(pname, enum_constsN))), [])
        in
          ml_isar_wrapper.define_simple_fun name
              ((map (mk_rec_eq name ((mk_Some atomT)$(Const(atomFQN^"."^secret_typeN, atomT)))) (map fst priv))
               @(map (mk_rec_eq name ((mk_Some atomT)$(Const(atomFQN^"."^other_pubconsts_typeN, atomT)))) (map fst pub_c))
               @[(Free(name, ctyp --> optionT atomT)
                           $(Const(fqn_name^"."^enumN, ctyp' --> ctyp)$(Term.dummy_pattern ctyp')),
                              (mk_Some atomT)$(Const(atomFQN^"."^enum_typeN,atomT)))]
               @(map (mk_rec_eq name (mk_None atomT)) (map fst pub_f)) ) lthy
        end

      fun def_ana lthy = let
        val pname = #name trac
        val (pub_f, pub_c, priv) = get_funs trac
        val pub = pub_f@pub_c
  
        val keyT = messageT' natT trac lthy
  
        val fqn_name = Local_Theory.full_name lthy (Binding.name (mkN(pname, funN)))
        val ctyp = Type(fqn_name, [])
    
        val ana_outputT = mk_prodT (mk_listT keyT, mk_listT natT)
  
        val default_output = mk_prod (mk_list keyT [], mk_list natT [])
  
        fun mk_ana_output ks rs = mk_prod (mk_list keyT ks, mk_list natT rs)
  
        fun mk_rec_eq name t fname = (Free(name, ctyp --> ana_outputT)
                                             $Term.Const(fqn_name^"."^fname,ctyp), t)
        val name = mkN(pname, anaN)
        val _ = info("  Defining "^name) 
        val ctyp' = Type(Local_Theory.full_name lthy (Binding.name (mkN(pname, enum_constsN))), [])
    
        val ana_spec =
          let
            val toInt = Option.valOf o Int.fromString
            fun ana_arity (f,n) = (if is_priv_fun trac f then (toInt n)-1 else toInt n)
            fun check_valid_arity ((f,ps),ks,rs) =
              case List.find (fn g => f = fst g) pub_f of
                SOME (f',n) =>
                  if length ps <> ana_arity (f',n)
                  then error ("Invalid number of parameters in the analysis rule for " ^ f ^
                              " (expected " ^ Int.toString (ana_arity (f',n)) ^
                              " but got " ^ Int.toString (length ps) ^ ")")
                  else ((f,ps),ks,rs)
              | NONE => error (f ^ " is not a declared function symbol of arity greater than zero")
            val transform_cMsg = transform_cMsg trac
            val rm_special_funs = rm_special_funs (fn ((f,_),_,_) => f)
            fun var_to_nat f xs x =
              let
                val n = snd (Option.valOf ((list_find (fn y => y = x) xs)))
              in
                if is_priv_fun trac f then mk_nat (1+n) else mk_nat n
              end
            fun c_to_h f xs t = ana_cMsg_to_hol (is_priv_fun trac f) t xs trac lthy
            fun keys f ps ks = map (c_to_h f ps o transform_cMsg o Trac_Term.certifyMsg [] []) ks
            fun results f ps rs = map (var_to_nat f ps) rs
            fun aux ((f,ps),ks,rs) = (f, mk_ana_output (keys f ps ks) (results f ps rs))
          in
            map (aux o check_valid_arity) (rm_special_funs (#analysis_spec trac))
          end

        val other_funs =
          filter (fn f => not (List.exists (fn g => f = g) (map fst ana_spec))) (map fst (pub@priv))
      in
        ml_isar_wrapper.define_simple_fun name
            ((map (fn (f,out) => mk_rec_eq name out f) ana_spec)
            @(map (mk_rec_eq name default_output) other_funs)
            @[(Free(name, ctyp --> ana_outputT)
                      $(Term.Const(fqn_name^"."^enumN, ctyp' --> ctyp)$(Term.dummy_pattern ctyp')),
                         default_output)]) lthy
      end

    in
      lthy |> def_atom 
           |> def_fun_dt
           |> def_fun_arity
           |> def_public
           |> def_gamma
           |> def_ana
    end

  fun define_term_model (trac:TracProtocol.protocol) lthy =
    let 
      val _ = info("Defining term model")
    in
      lthy |> snd o def_types trac 
           |> def_sets trac
           |> def_funs trac
    end
  
  fun define_fixpoint fp trac print lthy =
    let
      val fp_name = mkN (#name trac, "fixpoint")
      val _ = info("Defining fixpoint")
      val _ = info("  Defining "^fp_name)
      val fp_triple = transform_fp trac fp
      val fp_triple_trm = fp_triple_to_hol fp_triple trac lthy
      val trac = TracProtocol.update_fixed_point trac (SOME fp_triple)
    in
      (trac, #2 (ml_isar_wrapper.define_constant_definition' (fp_name, fp_triple_trm) print lthy))
    end

  fun define_protocol print ((trac:TracProtocol.protocol), lthy) = let
      val _ =
        if length (#transaction_spec trac) > 1
        then info("Defining protocols")
        else info("Defining protocol")
      val pname = #name trac

      val flat_type_spec = flatten_type_spec trac

      val mk_Transaction = mk_Transaction trac lthy

      val mk_Send = mk_Send_step trac lthy
      val mk_Receive = mk_Receive_step trac lthy
      val mk_InSet = mk_InSet_step trac lthy
      val mk_NotInSet = mk_NotInSet_step trac lthy
      val mk_Inequality = mk_Inequality_step trac lthy
      val mk_Insert = mk_Insert_step trac lthy
      val mk_Delete = mk_Delete_step trac lthy

      val star_label = mk_star_label
      val prot_label = mk_prot_label

      val certify_transation = TracProtocol.certifyTransaction

      fun mk_tname i (tr:TracProtocol.transaction_name) =
        let
          val x = #1 tr
          val y = case i of NONE => x | SOME n => mkN(n, x)
          val z = mkN("transaction", y)
        in mkN(pname, z)
        end

      fun def_transaction name_prefix prot_num (transaction:TracProtocol.cTransaction) lthy = let
        val defname = mk_tname name_prefix (#transaction transaction)
        val _ = info("  Defining "^defname)

        val receives     = #receive_actions     transaction
        val checkssingle = #checksingle_actions transaction
        val checksall    = #checkall_actions    transaction
        val updates      = #update_actions      transaction
        val sends        = #send_actions        transaction
        val fresh        = get_fresh_value_variables transaction
        val attack_signals = #attack_actions transaction

        val nonfresh_value_vars = get_nonfresh_value_variables transaction
        val value_vars = get_value_variables transaction
        val enum_vars  = get_enum_variables  transaction

        val (enum_ineqs, value_ineqs) = get_variable_restrictions transaction

        val transform_cMsg = transform_cMsg trac

        fun c_to_h trm = transaction_cMsg_to_hol (transform_cMsg trm) prot_num value_vars trac lthy

        val abstract_over_enum_vars = fn x => fn y => fn z =>
          abstract_over_enum_vars x y z flat_type_spec trac lthy

        fun mk_transaction_term (rcvs, chcksingle, chckall, upds, snds, frsh, atcks) =
          let
            open Trac_Term
            fun action_filter f (lbl,a) = case f a of SOME x => SOME (lbl,x) | NONE => NONE

            fun lbl_to_h (TracProtocol.LabelS) = star_label
              | lbl_to_h (TracProtocol.LabelN) = prot_label prot_num

            fun lbl_trm_to_h f (lbl,t) = f (lbl_to_h lbl) (c_to_h t)

            val S1 = map (lbl_trm_to_h mk_Receive)
                         (map_filter (action_filter TracProtocol.maybe_the_Receive) rcvs)

            val S2 =
              let
                fun aux (lbl,TracProtocol.cInequality (x,y)) =
                      SOME (mk_Inequality (lbl_to_h lbl) (c_to_h x) (c_to_h y))
                  | aux (lbl,TracProtocol.cInSet (e,s)) =
                      SOME (mk_InSet (lbl_to_h lbl) (c_to_h e) (c_to_h s))
                  | aux (lbl,TracProtocol.cNotInSet (e,s)) =
                      SOME (mk_NotInSet (lbl_to_h lbl) (c_to_h e) (c_to_h s))
                  | aux _ = NONE
              in
                map_filter aux chcksingle
              end

            val S3 =
              let
                fun arity s = case set_arity trac s of
                    SOME n => n
                  | NONE => error ("Not a set family: " ^ s)

                fun mk_evs s = map (fn n => ("X" ^ Int.toString n, "")) (0 upto ((arity s) -1))

                fun mk_trm (lbl,e,s) =
                  let
                    val ps = map (fn x => cVar (x,Untyped)) (map fst (mk_evs s))
                  in
                    mk_NotInSet (lbl_to_h lbl) (c_to_h e) (c_to_h (cSet (s,ps)))
                  end

                fun mk_trms (lbl,(e,s)) =
                  abstract_over_enum_vars (mk_evs s) [] (mk_trm (lbl,e,s))
              in
                map mk_trms (map_filter (action_filter TracProtocol.maybe_the_NotInAny) chckall)
              end

            val S4 = map (c_to_h o mk_Value_cVar) frsh

            val S5 =
              let
                fun aux (lbl,TracProtocol.cInsert (e,s)) =
                      SOME (mk_Insert (lbl_to_h lbl) (c_to_h e) (c_to_h s))
                  | aux (lbl,TracProtocol.cDelete (e,s)) =
                      SOME (mk_Delete (lbl_to_h lbl) (c_to_h e) (c_to_h s))
                  | aux _ = NONE
              in
                map_filter aux upds
              end

            val S6 =
              let val snds' = map_filter (action_filter TracProtocol.maybe_the_Send) snds
              in map (lbl_trm_to_h mk_Send) (snds'@map (fn (lbl,_) => (lbl,cAttack)) atcks) end
          in
            abstract_over_enum_vars enum_vars enum_ineqs (mk_Transaction S1 S2 S3 S4 S5 S6)
          end

        fun def_trm trm print lthy =
          #2 (ml_isar_wrapper.define_constant_definition' (defname, trm) print lthy)

        val additional_value_ineqs =
          let
            open Trac_Term
            open TracProtocol
            val poschecks = map_filter (maybe_the_InSet o snd) checkssingle
            val negchecks_single = map_filter (maybe_the_NotInSet o snd) checkssingle
            val negchecks_all = map_filter (maybe_the_NotInAny o snd) checksall

            fun aux' (cVar (x,ValueType),s) (cVar (y,ValueType),t) =
                  if s = t then SOME (x,y) else NONE
              | aux' _ _ = NONE

            fun aux (x,cSet (s,ps)) = SOME (
                  map_filter (aux' (x,cSet (s,ps))) negchecks_single@
                  map_filter (aux' (x,s)) negchecks_all
                )
              | aux _ = NONE
          in
            List.concat (map_filter aux poschecks)
          end

        val all_value_ineqs = mk_unique (value_ineqs@additional_value_ineqs)

        val valvarsprod =
              filter (fn p => not (List.exists (fn q => p = q orelse swap p = q) all_value_ineqs))
                     (list_triangle_product (fn x => fn y => (x,y)) nonfresh_value_vars)

        val transaction_trm0 = mk_transaction_term
                      (receives, checkssingle, checksall, updates, sends, fresh, attack_signals)
      in
        if null valvarsprod
        then def_trm transaction_trm0 print lthy
        else let
          val partitions = list_partitions nonfresh_value_vars all_value_ineqs
          val ps = filter (not o null) (map (filter (fn x => length x > 1)) partitions)

          fun mk_subst ps =
            let 
              open Trac_Term
              fun aux [] = NONE
                | aux (x::xs) = SOME (map (fn y => (y,cVar (x,ValueType))) xs)
            in
              List.concat (map_filter aux ps)
            end

          fun apply d =
            let
              val ap = TracProtocol.subst_apply_actions d
              fun f (TracProtocol.cInequality (x,y)) = x <> y
                | f _ = true
              val checksingle' = filter (f o snd) (ap checkssingle)
            in
              (ap receives, checksingle', ap checksall, ap updates, ap sends, fresh, attack_signals)
            end

          val transaction_trms = transaction_trm0::map (mk_transaction_term o apply o mk_subst) ps
          val transaction_typ = Term.fastype_of transaction_trm0

          fun mk_concat_trm tau trms =
            Term.Const (@{const_name "concat"}, mk_listT tau --> tau) $ mk_list tau trms
        in
          def_trm (mk_concat_trm transaction_typ transaction_trms) print lthy
        end
      end

      val def_transactions =
        let
          val prots = map (fn (n,pr) => map (fn tr => (n,tr)) pr) (#transaction_spec trac)
          val lbls = list_upto (length prots)
          val lbl_prots = List.concat (map (fn i => map (fn tr => (i,tr)) (nth prots i)) lbls)
          val f = fold (fn (i,(n,tr)) => def_transaction n i (certify_transation tr))
        in 
          f lbl_prots
        end

      fun def_protocols lthy = let
          fun mk_prot_def (name,trm) lthy =
            let val _ = info("  Defining "^name)
            in #2 (ml_isar_wrapper.define_constant_definition' (name,trm) print lthy)
            end

          val prots = #transaction_spec trac
          val num_prots = length prots

          val pdefname = mkN(pname, "protocol")

          fun mk_tnames i =
            let
              val trs = case nth prots i of (j,prot) => map (fn tr => (j,tr)) prot
            in map (fn (j,s) => full_name (mk_tname j (#transaction s)) lthy) trs
            end

          val tnames = List.concat (map mk_tnames (list_upto num_prots))

          val pnames =
            let
              val f = fn i => (Int.toString i,nth prots i)
              val g = fn (i,(n,_)) => case n of NONE => i | SOME m => m
              val h = fn s => mkN (pdefname,s)
            in map (h o g o f) (list_upto num_prots)
            end

          val trtyp = prot_transactionT trac lthy
          val trstyp = mk_listT trtyp
    
          fun mk_prot_trm names =
            Term.Const (@{const_name "concat"}, mk_listT trstyp --> trstyp) $
            mk_list trstyp (map (fn x => Term.Const (x, trstyp)) names)
    
          val lthy =
            if num_prots > 1
            then fold (fn (i,pname) => mk_prot_def (pname, mk_prot_trm (mk_tnames i)))
                      (map (fn i => (i, nth pnames i)) (list_upto num_prots))
                      lthy
            else lthy

          val pnames' = map (fn n => full_name n lthy) pnames

          fun mk_prot_trm_with_star i =
            let
              fun f j =
                if j = i
                then Term.Const (nth pnames' j, trstyp)
                else (Term.Const (@{const_name "map"}, [trtyp --> trtyp, trstyp] ---> trstyp) $
                      Term.Const ("Transactions.transaction_star_proj", trtyp --> trtyp) $
                      Term.Const (nth pnames' j, trstyp))
            in
              Term.Const (@{const_name "concat"}, mk_listT trstyp --> trstyp) $
              mk_list trstyp (map f (list_upto num_prots))
            end

          val lthy =
            if num_prots > 1
            then fold (fn (i,pname) => mk_prot_def (pname, mk_prot_trm_with_star i))
                      (map (fn i => (i, nth pnames i ^ "_with_star")) (list_upto num_prots))
                      lthy
            else lthy
      in
        mk_prot_def (pdefname, mk_prot_trm (if num_prots > 1 then pnames' else tnames)) lthy
      end
    in
      (trac, lthy |> def_transactions |> def_protocols)
    end
end
\<close>

ML\<open>
structure trac = struct
  open Trac_Term

  val info = Output.information
  (* Define global configuration option "trac" *)
  (* val trac_fp_compute_binary_cfg = 
      let
        val (trac_fp_compute_path_config, trac_fp_compute_path_setup) =
          Attrib.config_string (Binding.name "trac_fp_compute") (K "trac_fp_compute")
      in
        Context.>>(Context.map_theory trac_fp_compute_path_setup);
        trac_fp_compute_path_config
      end

  val trac_eval_cfg =
      let
        val (trac_fp_compute_eval_config, trac_fp_compute_eval) =
          Attrib.config_bool (Binding.name "trac_fp_compute_eval") (K false)
      in
        Context.>>(Context.map_theory trac_fp_compute_eval);
        trac_fp_compute_eval_config
      end *)

  type hide_tvar_tab = (TracProtocol.protocol) Symtab.table
  fun trac_eq (a, a') = (#name a) = (#name a')
  fun merge_trac_tab (tab,tab') = Symtab.merge trac_eq (tab,tab')
  structure Data = Generic_Data
  (
    type T = hide_tvar_tab
    val empty  = Symtab.empty:hide_tvar_tab
    val extend = I
    fun merge(t1,t2)  = merge_trac_tab (t1, t2)
  );

  fun update  p thy = Context.theory_of 
                        ((Data.map (fn tab => Symtab.update (#name p, p) tab) (Context.Theory thy)))
  fun lookup name thy = (Symtab.lookup ((Data.get o Context.Theory) thy) name,thy)

  fun mk_abs_filename thy filename =  
      let
        val filename = Path.explode filename
        val master_dir = Resources.master_directory thy
      in
        Path.implode (if (Path.is_absolute filename)
                      then filename
                      else master_dir + filename)
      end

  (* fun exec {trac_path, error_detail}  filename = let 
        open OS.FileSys OS.Process
 
        val tmpname = tmpName()
        val err_tmpname = tmpName()      
        fun plural 1 = "" | plural _ = "s"
        val trac = case trac_path of 
                         SOME s => s
                       | NONE   => raise error ("trac_fp_compute_path not specified")
        val cmdline = trac ^ " \"" ^ filename ^ "\" > " ^ tmpname ^ " 2> " ^ err_tmpname
      in
        if isSuccess (system cmdline) then (OS.FileSys.remove err_tmpname; tmpname)
        else let val _ = OS.FileSys.remove tmpname
                 val (msg, rest) = File.read_lines (Path.explode err_tmpname) |> chop error_detail
                 val _ = OS.FileSys.remove err_tmpname
                 val _ = warning ("trac failed on " ^ filename ^ "\nCommand: " ^ cmdline ^
                                  "\n\nOutput:\n" ^
                                  cat_lines (msg @ (if null rest then [] else
                                                    ["(... " ^ string_of_int (length rest) ^
                                                     " more line" ^ plural (length rest) ^ ")"])))
             in raise error ("trac failed on " ^ filename) end
      end *)

  fun lookup_trac (pname:string) lthy =
    Option.valOf (fst (lookup pname (Proof_Context.theory_of lthy)))

  fun def_fp fp_str print (trac, lthy) =
    let
      val fp = TracFpParser.parse_str fp_str
      val (trac,lthy) = trac_definitorial_package.define_fixpoint fp trac print lthy
      val lthy = Local_Theory.raw_theory (update trac) lthy
    in
      (trac, lthy)
    end

  fun def_fp_file filename print (trac, lthy) = let
        val thy = Proof_Context.theory_of lthy
        val abs_filename = mk_abs_filename thy filename
        val fp = TracFpParser.parse_file abs_filename
        val (trac,lthy) = trac_definitorial_package.define_fixpoint fp trac print lthy
        val lthy = Local_Theory.raw_theory (update trac) lthy
      in
        (trac, lthy)
      end

  fun def_fp_trac fp_filename print (trac, lthy) = let
        open OS.FileSys OS.Process
        val _ = info("Checking protocol specification with trac.")
        val thy = Proof_Context.theory_of lthy
        (* val trac =  Config.get_global thy trac_binary_cfg *)
        val abs_filename = mk_abs_filename thy fp_filename
        (* val fp_file = exec {error_detail=10, trac_path = SOME trac} abs_filename *)
        (* val fp_raw = File.read (Path.explode fp_file) *)
        val fp_raw = File.read (Path.explode abs_filename)
        val fp = TracFpParser.parse_str fp_raw
        (* val _ = OS.FileSys.remove fp_file *)
        val _ = if TracFpParser.attack fp 
                then 
                  error ("  ATTACK found, skipping generating of Isabelle/HOL definitions.\n\n")
                else 
                  info("  No attack found, continue with generating Isabelle/HOL definitions.")
        val (trac,lthy) = trac_definitorial_package.define_fixpoint fp trac print lthy
        val lthy = Local_Theory.raw_theory (update trac) lthy
      in
        (trac, lthy)
      end

  fun def_trac_term_model str lthy = let
        val trac = TracProtocolParser.parse_str str
        val lthy = Local_Theory.raw_theory (update trac) lthy
        val lthy = trac_definitorial_package.define_term_model trac lthy
      in
        (trac, lthy)
      end

  val def_trac_protocol = trac_definitorial_package.define_protocol

  fun def_trac str print = def_trac_protocol print o def_trac_term_model str

  fun def_trac_file filename print lthy = let
        val trac_raw = File.read (Path.explode filename)
        val (trac,lthy) = def_trac trac_raw print lthy
        val lthy = Local_Theory.raw_theory (update trac) lthy
      in
        (trac, lthy)
      end

  fun def_trac_fp_trac trac_str print lthy = let
        open OS.FileSys OS.Process
        val (trac,lthy) = def_trac trac_str print lthy
        val tmpname = tmpName()
        val _ = File.write (Path.explode tmpname) trac_str
        val (trac,lthy) = def_fp_trac tmpname print (trac, lthy)
        val _ = OS.FileSys.remove tmpname
        val lthy = Local_Theory.raw_theory (update trac) lthy
      in
        lthy
      end

end
\<close>

ML\<open>
  val fileNameP = Parse.name -- Parse.name

  val _ = Outer_Syntax.local_theory' @{command_keyword "trac_import"} 
          "Import protocol and fixpoint from trac files." 
          (fileNameP >> (fn (trac_filename, fp_filename) => fn print =>
             trac.def_trac_file trac_filename print #>
             trac.def_fp_file fp_filename print #> snd));

  val _ = Outer_Syntax.local_theory' @{command_keyword "trac_import_trac"}
          "Import protocol from trac file and compute fixpoint with trac." 
          (fileNameP >> (fn (trac_filename, fp_filename) => fn print =>
              trac.def_trac trac_filename print #> trac.def_fp_trac fp_filename print #> snd));

  val _ = Outer_Syntax.local_theory' @{command_keyword "trac_trac"}
          "Define protocol using trac format and compute fixpoint with trac."
          (Parse.cartouche >> (fn trac => fn print => trac.def_trac_fp_trac trac print));

  val _ = Outer_Syntax.local_theory' @{command_keyword "trac"}
          "Define protocol and (optionally) fixpoint using trac format."
          (Parse.cartouche -- Scan.optional Parse.cartouche "" >> (fn (trac,fp) => fn print =>
            if fp = ""
            then trac.def_trac trac print #> snd
            else trac.def_trac trac print #> trac.def_fp fp print #> snd));
\<close>

ML\<open>
val name_prefix_parser = Parse.!!! (Parse.name --| Parse.$$$ ":" -- Parse.name)

(* Original definition (opt_evaluator) copied from value_command.ml *)
val opt_proof_method_choice =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "safe";

(* Original definition (locale_expression) copied from parse_spec.ML *)
val opt_defs_list = Scan.optional
  (\<^keyword>\<open>for\<close> |-- Scan.repeat1 Parse.name >>
      (fn xs => if length xs > 3 then error "Too many optional arguments" else xs))
  [];

val security_proof_locale_parser =
  name_prefix_parser -- opt_defs_list

val security_proof_locale_parser_with_method_choice =
  opt_proof_method_choice -- name_prefix_parser -- opt_defs_list


fun protocol_model_setup_proof_state name prefix lthy =
  let
    fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z,[])))],[])
    val _ = if name = "" then error "No name given" else ()
    val pexpr = f "stateful_protocol_model" name (protocol_model_interpretation_params prefix)
    val pdefs = protocol_model_interpretation_defs name
    val proof_state = Interpretation.global_interpretation_cmd pexpr pdefs lthy
  in
    proof_state
  end

fun protocol_security_proof_proof_state manual_proof name prefix opt_defs print lthy =
  let
    fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z,[])))],[])
    val _ = if name = "" then error "No name given" else ()
    val num_defs = length opt_defs
    val pparams = protocol_model_interpretation_params prefix
    val default_defs = [prefix ^ "_" ^ "protocol", prefix ^ "_" ^ "fixpoint"]
    fun g locale_name extra_params = f locale_name name (pparams@map SOME extra_params)
    val (prot_fp_smp_names, pexpr) = if manual_proof
      then (case num_defs of
        0 => (default_defs, g "secure_stateful_protocol'" default_defs)
      | 1 => (opt_defs, g "secure_stateful_protocol''" opt_defs)
      | 2 => (opt_defs, g "secure_stateful_protocol'" opt_defs)
      | _ => (opt_defs, g "secure_stateful_protocol" opt_defs))
      else (case num_defs of
        0 => (default_defs, g "secure_stateful_protocol''''" default_defs)
      | 1 => (opt_defs, g "secure_stateful_protocol''" opt_defs)
      | 2 => (opt_defs, g "secure_stateful_protocol''''" opt_defs)
      | _ => (opt_defs, g "secure_stateful_protocol'''" opt_defs))
    val proof_state = lthy |> declare_protocol_checks print
                           |> Interpretation.global_interpretation_cmd pexpr []
  in
    (prot_fp_smp_names, proof_state)
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>protocol_model_setup\<close>
    "prove interpretation of protocol model locale into global theory"
    (name_prefix_parser >> (fn (name,prefix) => fn lthy =>
    let
      val proof_state = protocol_model_setup_proof_state name prefix lthy
      val meth =
        let
          val m = "protocol_model_interpretation"
          val _ = Output.information (
                    "Proving protocol model locale instance with proof method " ^ m)
        in
          Method.Source (Token.make_src (m, Position.none) [])
        end
    in
      ml_isar_wrapper.prove_state_simple meth proof_state
  end));

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>manual_protocol_model_setup\<close>
    "prove interpretation of protocol model locale into global theory"
    (name_prefix_parser >> (fn (name,prefix) => fn lthy =>
    let
      val proof_state = protocol_model_setup_proof_state name prefix lthy
      val subgoal_proof = "  subgoal by protocol_model_subgoal\n"
      val _ = Output.information ("Example proof:\n" ^
                Active.sendback_markup_command ("  apply unfold_locales\n"^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                "  done\n"))
    in
      proof_state
  end));

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>protocol_security_proof\<close>
    "prove interpretation of secure protocol locale into global theory"
    (security_proof_locale_parser_with_method_choice >> (fn params => fn print => fn lthy =>
    let
      val ((opt_meth_level,(name,prefix)),opt_defs) = params
      val (defs, proof_state) =
        protocol_security_proof_proof_state false name prefix opt_defs print lthy
      val num_defs = length defs
      val meth =
        let
          val m = case opt_meth_level of
              "safe" => "check_protocol" ^ "'" (* (if num_defs = 1 then "'" else "") *)
            | "unsafe" => "check_protocol_unsafe" ^ "'" (* (if num_defs = 1 then "'" else "") *)
            | _ => error ("Invalid option: " ^ opt_meth_level)
          val _ = Output.information (
                    "Proving security of protocol " ^ nth defs 0 ^ " with proof method " ^ m)
          val _ = if num_defs > 1 then Output.information ("Using fixpoint " ^ nth defs 1) else ()
          val _ = if num_defs > 2 then Output.information ("Using SMP set " ^ nth defs 2) else ()
        in
          Method.Source (Token.make_src (m, Position.none) [])
        end
    in
      ml_isar_wrapper.prove_state_simple meth proof_state
    end
    ));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>manual_protocol_security_proof\<close>
    "prove interpretation of secure protocol locale into global theory"
    (security_proof_locale_parser >> (fn params => fn print => fn lthy =>
    let
      val ((name,prefix),opt_defs) = params
      val (defs, proof_state) =
        protocol_security_proof_proof_state true name prefix opt_defs print lthy
      val subgoal_proof =
        let
          val m = "code_simp" (* case opt_meth_level of
              "safe" => "code_simp"
            | "unsafe" => "eval"
            | _ => error ("Invalid option: " ^ opt_meth_level) *)
        in
          "  subgoal by " ^ m ^ "\n"
        end
      val _ = Output.information ("Example proof:\n" ^
                Active.sendback_markup_command ("  apply check_protocol_intro\n"^
                                                subgoal_proof^
                                                (if length defs = 1 then ""
                                                 else subgoal_proof^
                                                      subgoal_proof^
                                                      subgoal_proof^
                                                      subgoal_proof)^
                                                "  done\n"))
    in
      proof_state
    end
    ));
\<close>

end
