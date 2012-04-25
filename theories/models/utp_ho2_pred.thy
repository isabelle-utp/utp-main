(******************************************************************************)
(* Title: utp/models/utp_ho2_pred.thy                                         *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho2_pred
imports "../GLOBAL" "../generic/utp_generic" utp_ho2_value
begin

section {* HO2 Predicates *}

(* TODO: This instantiation does not take into account HO consistency yet! *)

locale HO2_PRED =
  COMPOSITE_VALUE "basic_type_rel" "basic_value_ref" +
  TYPED_PRED
    "lift_type_rel_composite basic_type_rel"
    "lift_value_ref_composite basic_value_ref"
for basic_type_rel :: "'BASIC_VALUE :: BASIC_SORT \<Rightarrow> 'BASIC_TYPE \<Rightarrow> bool" and
  basic_value_ref :: "'BASIC_VALUE :: BASIC_SORT \<Rightarrow> 'BASIC_VALUE \<Rightarrow> bool"
begin

definition MkProg1 ::
  "PROG1_VALUE \<Rightarrow> HO2_VALUE" where
"MkProg1 = utp_ho2_value.MkProg1"

definition MkProg2 ::
  "PROG2_VALUE \<Rightarrow> HO2_VALUE" where
"MkProg2 = utp_ho2_value.MkProg2"

definition DestProg1 :: "HO2_VALUE \<Rightarrow> PROG1_VALUE" where
"DestProg1 = utp_ho2_value.DestProg1"

definition DestProg2 :: "HO2_VALUE \<Rightarrow> PROG2_VALUE" where
"DestProg2 = utp_ho2_value.DestProg2"

definition IsProg1 :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg1 = utp_ho2_value.IsProg1Val"

definition IsProg2 :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg2 = utp_ho2_value.IsProg2Val"

declare MkProg1_def [simp]
declare MkProg2_def [simp]
declare DestProg1_def [simp]
declare DestProg2_def [simp]
declare IsProg1_def [simp]
declare IsProg2_def [simp]
end

interpretation HO2 :
  HO2_PRED
    "lift_type_rel_composite ho2_type_rel"
    "lift_value_ref_composite ho2_value_ref"
apply (simp add: HO2_PRED_def)
apply (auto)
done

subsection {* Definitions *}

definition HO2_VALUE [simp] :
"HO2_VALUE = HO2.universe"

definition HO2_ALPHABET [simp] :
"HO2_ALPHABET \<equiv> HO2.WF_ALPHABET"

definition HO2_BINDING [simp] :
"HO2_BINDING \<equiv> WT_BINDING ho2_type_rel"

definition HO2_BINDING_SET [simp] :
"HO2_BINDING_SET \<equiv> HO2.WF_BINDING_SET"

definition HO2_BINDING_FUN [simp] :
"HO2_BINDING_FUN \<equiv> HO2.WF_BINDING_FUN"

definition HO2_PREDICATE [simp] :
"HO2_PREDICATE \<equiv> HO2.WF_ALPHA_PREDICATE"

definition HO2_FUNCTION [simp] :
"HO2_FUNCTION \<equiv> HO2.WF_ALPHA_FUNCTION"

subsection {* Global Syntax *}

subsubsection {* Value Syntax *}

defs HO2_type_rel [simp] :
"GLOBAL.type_rel \<equiv> lift_type_rel_composite ho2_type_rel"

defs HO2_set_type_rel [simp] :
"GLOBAL.set_type_rel \<equiv> HO2.set_type_rel"

defs HO2_value_ref [simp] :
"GLOBAL.value_ref \<equiv> lift_value_ref_composite ho2_value_ref"

subsubsection {* Predicate Syntax *}

defs HO2_alphabet [simp] :
"GLOBAL.alphabet \<equiv> HO2.alphabet"

defs HO2_bindings [simp] :
"GLOBAL.bindings \<equiv> HO2.bindings"

defs HO2_BINDING_EQUIV [simp] :
"GLOBAL.BINDING_EQUIV \<equiv> HO2.BINDING_EQUIV"

defs HO2_LiftP [simp] :
"GLOBAL.LiftP \<equiv> HO2.LiftP"

defs HO2_TrueP [simp] :
"GLOBAL.TrueP \<equiv> HO2.TrueP"

defs HO2_FalseP [simp] :
"GLOBAL.FalseP \<equiv> HO2.FalseP"

defs HO2_TRUE [simp] :
"GLOBAL.TRUE \<equiv> HO2.TRUE"

defs HO2_FALSE [simp] :
"GLOBAL.FALSE \<equiv> HO2.FALSE"

defs HO2_ExtP [simp] :
"GLOBAL.ExtP \<equiv> HO2.ExtP"

defs HO2_ResP [simp] :
"GLOBAL.ResP \<equiv> HO2.ResP"

defs HO2_NotP [simp] :
"GLOBAL.NotP \<equiv> HO2.NotP"

defs HO2_AndP [simp] :
"GLOBAL.AndP \<equiv> HO2.AndP"

defs HO2_OrP [simp] :
"GLOBAL.OrP \<equiv> HO2.OrP"

defs HO2_ImpliesP [simp] :
"GLOBAL.ImpliesP \<equiv> HO2.ImpliesP"

defs HO2_IffP [simp] :
"GLOBAL.IffP \<equiv> HO2.IffP"

defs HO2_ExistsResP [simp] :
"GLOBAL.ExistsResP \<equiv> HO2.ExistsResP"

defs HO2_ForallResP [simp] :
"GLOBAL.ForallResP \<equiv> HO2.ForallResP"

defs HO2_ExistsP [simp] :
"GLOBAL.ExistsP \<equiv> HO2.ExistsP"

defs HO2_ForallExtP [simp] :
"GLOBAL.ForallP \<equiv> HO2.ForallP"

defs HO2_ClosureP [simp] :
"GLOBAL.ClosureP \<equiv> HO2.ClosureP"

defs HO2_RefP [simp] :
"GLOBAL.RefP \<equiv> HO2.RefP"

defs HO2_Tautology [simp] :
"GLOBAL.Tautology \<equiv> HO2.Tautology"

defs HO2_Contradiction [simp] :
"GLOBAL.Contradiction \<equiv> HO2.Contradiction"

defs HO2_Contingency [simp] :
"GLOBAL.Contingency \<equiv> HO2.Contingency"

defs HO2_Refinement [simp] :
"GLOBAL.Refinement \<equiv> HO2.Refinement"

subsection {* Proof Experiments *}

text {* Value Proofs *}

theorem
"HO2.MkInt(1) +v HO2.MkInt(2) = HO2.MkInt(3)"
apply (simp)
done

theorem
"HO2.MkInt(1) \<in>v HO2.MkSet({HO2.MkInt(1), HO2.MkInt(2)})"
apply (simp)
done

theorem
"HO2.MkInt(3) \<in>v
 HO2.MkSet({HO2.MkInt(1)}) \<union>v HO2.MkSet({HO2.MkInt(1) +v HO2.MkInt(2)})"
apply (simp)
done

text {* Predicate Proofs *}

theorem
"\<lbrakk>p1 \<in> HO2_PREDICATE;
 p2 \<in> HO2_PREDICATE;
 p3 \<in> HO2_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p (p2 \<and>p p3) = (p1 \<and>p p2) \<and>p p3"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem
"\<lbrakk>p1 \<in> HO2_PREDICATE;
 p2 \<in> HO2_PREDICATE\<rbrakk> \<Longrightarrow>
 taut p1 \<and>p p2 \<Rightarrow>p p1"
apply (utp_pred_taut_tac)
done

theorem
"\<lbrakk>p1 \<in> HO2_PREDICATE;
 p2 \<in> HO2_PREDICATE;
 \<alpha> p1 = \<alpha> p2\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<sqsubseteq> p1"
apply (simp)
apply (utp_pred_taut_tac)
done
end
