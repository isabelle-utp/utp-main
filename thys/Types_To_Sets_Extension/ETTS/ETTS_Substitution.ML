(* Title: ETTS/ETTS_Substitution.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the functionality associated with the sbterms.
*)

signature ETTS_SUBSTITUTION =
sig
val sbt_data_of : Proof.context -> Ctermtab.key -> thm option
val is_sbt_data_key : Proof.context -> cterm -> bool
val process_tts_register_sbts : 
  string * string list -> Proof.context -> Proof.state
end;


structure ETTS_Substitution : ETTS_SUBSTITUTION =
struct




(**** Prerequisites ****)

open ETTS_Utilities;
open ETTS_RI;




(**** Data containers ****)



(*** Data ***)

structure SBTData_Args =
struct
  type T = thm Ctermtab.table
  val empty = Ctermtab.empty
  val extend = I
  val merge : (T * T -> T) = Ctermtab.merge (K true)
  fun init _ = Ctermtab.empty
end;
structure Global_SBTData = Theory_Data (SBTData_Args);
structure Local_SBTData = Proof_Data (SBTData_Args);



(*** Generic operations ***)

val sbt_data_of = Local_SBTData.get #> Ctermtab.lookup;
val sbt_data_keys = Local_SBTData.get #> Ctermtab.keys
fun map_sbt_data f (Context.Proof ctxt) = ctxt 
      |> Local_SBTData.map f 
      |> Context.Proof 
  | map_sbt_data f (Context.Theory thy) = thy 
      |> Global_SBTData.map f 
      |> Context.Theory;
fun update_sbt_data k v =
  let
    fun declaration phi = (Morphism.cterm phi k, Morphism.thm phi v) 
      |> Ctermtab.update 
      |> map_sbt_data
  in Local_Theory.declaration {pervasive=true, syntax=false}  declaration end;

fun is_sbt_data_key ctxt ct = member (op aconvc) (sbt_data_keys ctxt) ct;



(**** Evaluation : tts_find_sbts *****)

fun process_tts_find_sbts args st = 
  let 
    val ctxt = Toplevel.context_of st
    val args = case args of
        [] => sbt_data_keys ctxt
      | args => map (ctxt |> Syntax.read_term #> Thm.cterm_of ctxt) args
  in
    args
    |> map (sbt_data_of ctxt #> the #> Thm.string_of_thm ctxt |> apdupr)
    |> map (Thm.term_of #> Syntax.string_of_term ctxt |> apfst) 
    |> map ((fn (c, thmc) => c ^ " : " ^ thmc) #> writeln)
    |> K ()
  end;




(**** Parser : tts_find_sbts ****)

val parse_tts_find_sbts = Parse.and_list Parse.term;




(**** Interface : tts_find_sbts *****)

val _ = Outer_Syntax.command
  \<^command_keyword>\<open>tts_find_sbts\<close>
  "lookup a theorem associated with a constant or a fixed variable"
  (parse_tts_find_sbts >> (process_tts_find_sbts #> Toplevel.keep));




(**** Evaluation : tts_register_sbts *****)

local 

fun mk_msg_tts_register_sbts msg = "tts_register_sbts: " ^ msg;

(*create the goals for the function register_sbts_cmd*)
fun mk_goal_register_sbts ctxt sbt risset =
  let

    val msg_repeated_risset = mk_msg_tts_register_sbts
      "the type variables associated with the risset must be distinct"

    (*auxiliary functions*)
    fun mk_rel_assms (brelt, rissett) = 
      [
        mk_Domainp_sc brelt rissett, 
        Transfer.mk_bi_unique brelt, 
        Transfer.mk_right_total brelt
      ];

    (*risset \<rightarrow> unique ftvs of risset*)
    val rissetftv_specs = map (type_of #> dest_rissetT) risset

    (*input verification*)
    val _ = rissetftv_specs 
      |> has_duplicates op= 
      |> not orelse error msg_repeated_risset

    (*sbt \<rightarrow> (sbt, ftvs of sbt)*)
    val sbt = sbt |> (type_of #> (fn t => Term.add_tfreesT t []) |> apdupr)

    (*
      (sbt, ftvs of sbt), rissetftv_specs \<rightarrow> 
        ((sbtftv_int, rcdftv_int)s, (sbtftv_sub, rcdftv_sub)s), ctxt),
      where
        sbtftv_ints = unique ftvs of sbt \<inter> ftvs of risset
        sbtftv_subs = unique ftvs of sbt - ftvs of risset
    *)
    val (sbtftv_specs, ctxt) = 
      let
        fun mk_ri_rhs_Ts ctxt f = map (apdupr f)
          #> map_slice_side_r (fn Ss => Variable.invent_types Ss ctxt)
      in
        sbt 
        |> #2  
        |> distinct op=
        |> dup
        |>> inter op= rissetftv_specs
        ||> subtract op= rissetftv_specs
        |>> mk_ri_rhs_Ts ctxt (K \<^sort>\<open>HOL.type\<close>) 
        |>> swap
        |> reroute_ps_sp     
        |> swap
        |>> apsnd (map dup)
      end

    (*(sbt, ftvs of sbt) \<rightarrow> (sbt, sbtftv_ints)*)
    val sbt = apsnd (filter (member op= (sbtftv_specs |> #1 |> map #1))) sbt

    (* 
      (sbtftv_int, rcdftv_int)s, sbtftv_subs) \<rightarrow> 
        (((sbtftv, rcdftv), ri brel)s, ctxt) 
    *)
    val (sbtftv_specs, ctxt') =
      let val un_of_typ = #1 #> term_name_of_type_name 
      in 
        sbtftv_specs
        |>> map (apfst un_of_typ #> apsnd un_of_typ |> apdupr)
        |>> map (apsnd op^) 
        |>> map_slice_side_r (fn cs => Variable.variant_fixes cs ctxt)
        |>> (apfst TFree #> apsnd TFree |> apdupr |> apfst |> map |> apfst) 
        |>> (reroute_ps_sp |> map |> apfst)
        |>> (swap #> HOLogic.mk_rel |> apsnd |> map |> apfst)
        |>> swap
        |> reroute_ps_sp
        |> swap
        |>> (#1 #> TFree #> HOLogic.eq_const |> apdupr |> map |> apsnd)
      end
    
    (*((sbtftv, rcdftv), ri brel)s, ctxt  \<rightarrow> (premises, conclusion)*)
    val sbt_specs =
      let 
        val ftv_map = sbtftv_specs 
          |> #1
          |> map (apfst #1)
          |> AList.lookup op= #> the
        val ftv_map' = sbtftv_specs 
          |> op@
          |> map (apfst #1)
        val risset_of_ftv_spec = ((risset |> map (type_of #> dest_rissetT)) ~~ risset)
          |> AList.lookup op=
        val map_specTs_to_rcdTs = sbtftv_specs
          |> op@
          |> map (#1 #> apsnd TFree)
          |> AList.lookup op= #> the
        val (rct_name, ctxt'') = ctxt' 
          |> Variable.variant_fixes (single "rcdt")
          |>> the_single
      in
        sbt
        |> 
          (
            (
              ftv_map |> apdupl 
              #> (risset_of_ftv_spec #> the |> apsnd)
              #> mk_rel_assms
              |> map 
              #> flat
              #> map HOLogic.mk_Trueprop
              |> apsnd
            )
            #> (#1 #> type_of |> apdupl)
            #> (ftv_map' |> CTR_Relators.pr_of_typ ctxt'' |> apfst)
          )
        |> (fn x => (x, rct_name))
        |> 
          (
            (#1 #> #2 #> #1 #> type_of |> apdupr)
            #> (map_specTs_to_rcdTs |> map_type_tfree |> apsnd)
            #> reroute_ps_sp 
            #> (Free |> apdupl |> apsnd) 
          )
        |> reroute_sp_ps
        |> 
          (
            apfst reroute_sp_ps 
            #> reroute_ps_sp 
            #> apsnd swap 
            |> apfst
            #> apfst reroute_sp_ps 
            #> reroute_ps_sp 
            #> apsnd swap  
            #> reroute_sp_ps 
          )
        |> 
          (
            apfst op$ 
            #> op$ 
            |> apfst
            #> swap
            #> reroute_ps_triple 
            #> HOLogic.mk_exists 
            #> HOLogic.mk_Trueprop
            #> Syntax.check_term ctxt''
            |> apfst 
          )
        |> swap  
      end

    (*introduce the side conditions for each ex_pr*)
    val goal = 
      let
        fun add_premts (premts, conclt) = fold_rev 
          (fn premt => fn t => Logic.mk_implies (premt, t)) 
          premts
          conclt
      in add_premts sbt_specs end

   in (goal, ctxt') end 

in

(*implementation of the functionality of the command tts_register_sbts*)
fun process_tts_register_sbts args ctxt = 
  let 

    (*error messages*)

    val msg_fv_not_fixed = mk_msg_tts_register_sbts
      "all fixed variables that occur in the sbterm " ^
      "must be fixed in the context"
    val msg_ftv_not_fixed = mk_msg_tts_register_sbts
      "all fixed type variables that occur in the sbterm " ^
      "must be fixed in the context"
    val msg_sv = mk_msg_tts_register_sbts
      "the sbterm must contain no schematic variables"
    val msg_stv = mk_msg_tts_register_sbts
      "the sbterm must contain no schematic type variables"

    (*pre-processing and input verification*) 
   
    val sbt = args 
      |> #1 
      |> Syntax.read_term ctxt
    val risset = args
      |> #2
      |> map (Syntax.read_term ctxt)

    val _ = ETTS_RI.risset_input ctxt "tts_register_sbts" risset
    
    val _ = sbt
      |> (fn t => Term.add_frees t [])
      |> distinct op=
      |> map #1
      |> map (Variable.is_fixed ctxt)
      |> List.all I
      orelse error msg_fv_not_fixed
    val _ = sbt
      |> (fn t => Term.add_tfrees t [])
      |> distinct op=
      |> map #1
      |> map (Variable.is_declared ctxt)
      |> List.all I
      orelse error msg_ftv_not_fixed
    val _ = sbt
      |> (fn t => Term.add_vars t [])
      |> length
      |> curry op= 0
      orelse error msg_sv
    val _ = sbt
      |> (fn t => Term.add_tvars t [])
      |> length
      |> curry op= 0
      orelse error msg_stv

    (*main*)

    val (goalt, _) = mk_goal_register_sbts ctxt sbt risset
    val goal_specs = (goalt, []) |> single |> single

    val ct = Thm.cterm_of ctxt sbt

    fun after_qed thmss lthy = update_sbt_data ct (thmss |> hd |> hd) lthy

  in Proof.theorem NONE after_qed goal_specs ctxt end;

end;




(**** Parser : tts_register_sbts ****)

val parse_tts_register_sbts =
  Parse.term -- (\<^keyword>\<open>|\<close> |-- Parse.and_list Parse.term);




(**** Interface : tts_register_sbts ****)

val _ = Outer_Syntax.local_theory_to_proof
  \<^command_keyword>\<open>tts_register_sbts\<close>
  "command for the registration of the set-based terms"
  (parse_tts_register_sbts >> process_tts_register_sbts)

end;