(* Title: CTR_Tools/More_Thm.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Thm from the standard library of 
Isabelle/Pure.
*)

signature THM =
sig
  include THM
  val unvarify_local_fact : 
    Proof.context -> thm list -> thm list * Proof.context
  val unvarify_local_thm : Proof.context -> thm -> thm * Proof.context
  val unvarify_local_thms : 
    Proof.context -> thm list -> thm list * Proof.context
  val tags_rule : (string * string) list -> thm -> thm
  val apply_attributes: 
    attribute list -> thm list -> Context.generic -> thm list * Context.generic 
  val forall_intr_var_order : Proof.context -> int list -> thm -> thm
  val pure_unfold : Proof.context -> thm list -> thm -> thm
end;

structure Thm: THM =
struct

open Thm;

(* 
unvarify a fact in a local context (new (type) variables are 
fixed and declared in the context).
*)
fun unvarify_local_fact ctxt thms =
  let
    val thmts = map Thm.full_prop_of thms
    val stv_specs = thmts
      |> map (fn thmt => Term.add_tvars thmt [] |> rev) 
      |> flat
      |> distinct op=
    val ctxt' = fold Proof_Context.augment thmts ctxt
    val (ftv_specs, ctxt'') = Variable.invent_types (map #2 stv_specs) ctxt'
    val ctxt''' = fold Variable.declare_typ (map TFree ftv_specs) ctxt
    val stv_to_ftv = stv_specs ~~ ftv_specs |> AList.lookup op= #> the
    val instT = map (fn v => (v, v |> stv_to_ftv |> TFree)) stv_specs
    val sv_specs = thmts
      |> map (fn thmt => Term.add_vars thmt [] |> rev) 
      |> flat 
      |> distinct op=
    val ftvcs = 
      let
        val stvcs = sv_specs 
          |> map (#1 #> #1)
          |> Variable.variant_name_const ctxt''
          |> rev
      in Variable.variant_fixes stvcs ctxt'' |> #1 end
    val ctxt'''' = Variable.add_fixes ftvcs ctxt''' |> #2
    val insts = 
      let val stvc_to_ftvc = AList.lookup op= (sv_specs ~~ ftvcs) #> the
      in
        map 
          (
            fn v as ((a, i), T) =>
              let val T' = Term_Subst.instantiateT instT T
              in 
                (
                  ((a, i), T'), 
                  ((stvc_to_ftvc v, T') |> Free |> Thm.cterm_of ctxt'''')
                ) 
              end
          )
          sv_specs
      end
    val ctxt''''' = ctxt''''
      |> fold Variable.declare_term (map (#2 #> Thm.term_of) insts) 
    val thms' = 
      map 
        (
          Drule.instantiate_normalize 
            (map (apsnd (Thm.ctyp_of ctxt)) instT, insts)
        ) 
        thms     
  in (thms', ctxt''''') end;

(*unvarify a single theorem in a local context*)
fun unvarify_local_thm ctxt thm = thm
  |> single
  |> unvarify_local_fact ctxt
  |>> the_single;

(*unvarify a list of theorems in a local context*)
fun unvarify_local_thms ctxt thms =
  let
    fun folder thm (thms, ctxt) = thm
      |> single
      |> unvarify_local_fact ctxt 
      |>> the_single
      |>> curry (swap #> op::) thms;
  in fold_rev folder thms ([], ctxt) end;

(*add multiple tags*)
fun tags_rule tgs thm = fold Thm.tag_rule tgs thm;

(*apply a list of attributes to a fact*)
fun apply_attributes attrs thms context =
  let 
    fun apply_attributes_single attrs thm context = 
      fold 
      (fn attr => fn (thm, context) => Thm.apply_attribute attr thm context) 
      attrs 
      (thm, context);
    fun folder thm (thms, context) = context
      |> apply_attributes_single attrs thm 
      |>> curry (op:: o swap) thms;
  in fold folder thms ([], context) |>> rev end;

(*introduction of the universally quantified variables with respect to a 
pre-defined order on the stvs*)
fun forall_intr_var_order ctxt order thm' =
  let
    val stvs = thm'
      |> Thm.full_prop_of
      |> (fn t => Term.add_vars t [])
      |> rev
    val stv_cts = map (nth stvs #> Var #> Thm.cterm_of ctxt) order 
  in fold Thm.forall_intr (rev stv_cts) thm' end;

(*low level unfold*)
(*Designed based on an algorithm from HOL-Types_To_Sets/unoverload_def.ML*)
fun pure_unfold ctxt thms = ctxt
  |> 
    (
      thms
      |> Conv.rewrs_conv 
      |> Conv.try_conv 
      |> K
      |> Conv.top_conv
    )
  |> Conv.fconv_rule;

end;