(* Copyright 2021 (C) Mihails Milehins *)

signature IDE =
sig

val mk_intro : Proof.context -> thm -> thm list
val mk_dest : Proof.context -> thm -> thm list
val mk_elim : Proof.context -> thm -> thm list

end;

structure IDE: IDE  =
struct



(*** Auxiliary ***)

fun is_conj (Const (\<^const_name>\<open>conj\<close>, _) $ _ $ _) = true
  | is_conj _ = false;

fun is_equals (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _) = true
  | is_equals _ = false;



(*** Introduction rule ***)

fun mk_intro ctxt thm =
  let 
    val thm' = thm RS @{thm verit_Pure_trans}
    val n = Thm.nprems_of thm'
  in 
    thm'
    |> rotate_prems (n - 1)
    |> Local_Defs.unfold ctxt (single @{thm conj_imp_eq_imp_imp}) 
    |> single 
  end;



(*** Destruction rule ***)

local 

fun is_conj_concl thm = thm
  |> Thm.concl_of
  |> HOLogic.dest_Trueprop
  |> is_conj

fun dest_conj_concl_impl [] = []
  | dest_conj_concl_impl (thm :: thms) = 
    if is_conj_concl thm 
    then 
      let
        val thm2 = thm RS conjunct2
        val thm1 = thm RS conjunct1
      in
        (if is_conj_concl thm2 then dest_conj_concl_impl [thm2] else [thm2]) @ 
        (if is_conj_concl thm1 then dest_conj_concl_impl [thm1] else [thm1]) @ 
        dest_conj_concl_impl thms
      end
    else thm :: dest_conj_concl_impl thms;

in

fun mk_dest ctxt thm =
  let 
    val thm' = Local_Defs.unfold ctxt (single @{thm conj_assoc}) thm
    val thm'' = thm' RS @{thm PQ_P_Q}
    val n = Thm.nprems_of thm''
    val thm''' = thm'' 
      |> rotate_prems (n - 1) 
      |> Local_Defs.unfold ctxt (single @{thm conj_imp_eq_imp_imp});
  in dest_conj_concl_impl [thm'''] |> rev end;

end;



(*** Elimination rule ***)

fun mk_elim ctxt thm = 
  let
    val thm' = (thm RS @{thm PQ_P_Q})
      |> Tactic.make_elim
      |> Local_Defs.unfold ctxt (single @{thm conj_imp_eq_imp_imp})
    val conclt = Thm.concl_of thm'
    val conclt' = conclt
      |> dest_Var
      ||> K \<^typ>\<open>bool\<close>
      |> Var
      |> HOLogic.mk_Trueprop
    val insts = (conclt, conclt')
      |> apply2 (Thm.cterm_of ctxt)
      |> Thm.first_order_match 
  in thm' |> Drule.instantiate_normalize insts |> single end;



(*** Command ***)

val error_msg = "mk_ide: invalid arguments"

val mk_ide_parser = Scan.option \<^keyword>\<open>rf\<close> -- Parse.thm --
  (
    Scan.repeat
      (
        (\<^keyword>\<open>|intro\<close> -- Parse_Spec.opt_thm_name "|") ||
        (\<^keyword>\<open>|dest\<close> -- Parse_Spec.opt_thm_name "|") ||
        (\<^keyword>\<open>|elim\<close> -- Parse_Spec.opt_thm_name "|")
      )
  );

fun process_mk_rule mk_rule ((rf, b), thm) ctxt =
  let 
    val thms = thm
      |> mk_rule ctxt 
      |> 
        (
          fn thms => 
            if is_some rf 
            then map (Object_Logic.rulify ctxt) thms 
            else thms
        )
    val ((c, thms'), ctxt') = 
      Local_Theory.note (b ||> map (Attrib.check_src ctxt), thms) ctxt
    val _ = IDE_Utilities.thm_printer ctxt' true c thms'
  in ctxt' end;

fun folder_mk_rule (("|intro", b), (rf, thm)) ctxt =
      process_mk_rule mk_intro ((rf, b), thm) ctxt
  | folder_mk_rule (("|dest", b), (rf, thm)) ctxt =
      process_mk_rule mk_dest ((rf, b), thm) ctxt
  | folder_mk_rule (("|elim", b), (rf, thm)) ctxt = 
      process_mk_rule mk_elim ((rf, b), thm) ctxt
  | folder_mk_rule _ _ = error error_msg

fun process_mk_ide ((rf, thm), ins) ctxt =
  let
    val _ = ins |> map #1 |> has_duplicates op= |> not orelse error error_msg
    val thm' = thm
      |> singleton (Attrib.eval_thms ctxt) 
      |> Local_Defs.meta_rewrite_rule ctxt;
    val t = Thm.concl_of thm' 
    val _ = t |> is_equals orelse error error_msg
    val _ = (t |> Logic.dest_equals |> #1 |> type_of |> body_type) = \<^typ>\<open>bool\<close> 
      orelse error error_msg
  in fold folder_mk_rule (map (fn x => (x, (rf, thm'))) ins) ctxt end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>mk_ide\<close> 
    "synthesis of the intro/dest/elim rules" 
    (mk_ide_parser >> process_mk_ide);

end;