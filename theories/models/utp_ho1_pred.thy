(******************************************************************************)
(* Title: utp/models/utp_ho1_pred.thy                                         *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho1_pred
imports "../GLOBAL" "../generic/utp_generic" utp_ho1_value
begin

section {* HO1 Predicates *}

locale HO1_PRED =
  HO1_VALUE_LOCALE + TYPED_PRED "ho1_type_rel"

interpretation HO1 : HO1_PRED
apply (unfold HO1_PRED_def HO1_VALUE_LOCALE_def)
apply (auto)
done

subsection {* Semantic Domains *}

definition HO1_VALUE [simp] :
"HO1_VALUE = HO1.universe"

definition HO1_ALPHABET [simp] :
"HO1_ALPHABET \<equiv> HO1.WF_ALPHABET"

definition HO1_BINDING [simp] :
"HO1_BINDING \<equiv> WT_BINDING ho1_type_rel"

definition HO1_BINDING_SET [simp] :
"HO1_BINDING_SET \<equiv> HO1.WF_BINDING_SET"

definition HO1_BINDING_FUN [simp] :
"HO1_BINDING_FUN \<equiv> HO1.WF_BINDING_FUN"

definition HO1_PREDICATE [simp] :
"HO1_PREDICATE \<equiv> HO1.WF_ALPHA_PREDICATE"

definition HO1_FUNCTION [simp] :
"HO1_FUNCTION \<equiv> HO1.WF_ALPHA_FUNCTION"

subsection {* Global Syntax *}

subsubsection {* Value Syntax *}

text {* Should the following be done in the theory @{text utp_ho1_value}? *}

defs HO1_type_rel [simp] :
"GLOBAL.type_rel \<equiv> ho1_type_rel"

defs HO1_set_type_rel [simp] :
"GLOBAL.set_type_rel \<equiv> HO1.set_type_rel"

subsubsection {* Predicate Syntax *}

defs HO1_alphabet [simp] :
"GLOBAL.alphabet \<equiv> HO1.alphabet"

defs HO1_bindings [simp] :
"GLOBAL.bindings \<equiv> HO1.bindings"

defs HO1_binding_equiv [simp] :
"GLOBAL.binding_equiv \<equiv> HO1.binding_equiv"

defs HO1_LiftP [simp] :
"GLOBAL.LiftP \<equiv> HO1.LiftP"

defs HO1_TrueP [simp] :
"GLOBAL.TrueP \<equiv> HO1.TrueP"

defs HO1_FalseP [simp] :
"GLOBAL.FalseP \<equiv> HO1.FalseP"

defs HO1_TRUE [simp] :
"GLOBAL.TRUE \<equiv> HO1.TRUE"

defs HO1_FALSE [simp] :
"GLOBAL.FALSE \<equiv> HO1.FALSE"

defs HO1_ExtP [simp] :
"GLOBAL.ExtP \<equiv> HO1.ExtP"

defs HO1_ResP [simp] :
"GLOBAL.ResP \<equiv> HO1.ResP"

defs HO1_NotP [simp] :
"GLOBAL.NotP \<equiv> HO1.NotP"

defs HO1_AndP [simp] :
"GLOBAL.AndP \<equiv> HO1.AndP"

defs HO1_OrP [simp] :
"GLOBAL.OrP \<equiv> HO1.OrP"

defs HO1_ImpliesP [simp] :
"GLOBAL.ImpliesP \<equiv> HO1.ImpliesP"

defs HO1_IffP [simp] :
"GLOBAL.IffP \<equiv> HO1.IffP"

defs HO1_ExistsResP [simp] :
"GLOBAL.ExistsResP \<equiv> HO1.ExistsResP"

defs HO1_ForallResP [simp] :
"GLOBAL.ForallResP \<equiv> HO1.ForallResP"

defs HO1_ExistsP [simp] :
"GLOBAL.ExistsP \<equiv> HO1.ExistsP"

defs HO1_ForallExtP [simp] :
"GLOBAL.ForallP \<equiv> HO1.ForallP"

defs HO1_ClosureP [simp] :
"GLOBAL.ClosureP \<equiv> HO1.ClosureP"

defs HO1_RefP [simp] :
"GLOBAL.RefP \<equiv> HO1.RefP"

defs HO1_Tautology [simp] :
"GLOBAL.Tautology \<equiv> HO1.Tautology"

defs HO1_Contradiction [simp] :
"GLOBAL.Contradiction \<equiv> HO1.Contradiction"

defs HO1_Contingency [simp] :
"GLOBAL.Contingency \<equiv> HO1.Contingency"

defs HO1_Refinement [simp] :
"GLOBAL.Refinement \<equiv> HO1.Refinement"

subsection {* Proof Experiments *}

text {* Value Proofs *}

theorem
"HO1.MkInt(1) +v HO1.MkInt(2) = HO1.MkInt(3)"
apply (simp)
done

theorem
"HO1.MkInt(1) \<in>v HO1.MkSet({HO1.MkInt(1), HO1.MkInt(2)})"
apply (simp)
done

theorem
"HO1.MkInt(3) \<in>v
 HO1.MkSet({HO1.MkInt(1)}) \<union>v HO1.MkSet({HO1.MkInt(1) +v HO1.MkInt(2)})"
apply (simp)
done

text {* Predicate Proofs *}

theorem
"\<lbrakk>p1 \<in> HO1_PREDICATE;
 p2 \<in> HO1_PREDICATE;
 p3 \<in> HO1_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p (p2 \<and>p p3) = (p1 \<and>p p2) \<and>p p3"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem
"\<lbrakk>p1 \<in> HO1_PREDICATE;
 p2 \<in> HO1_PREDICATE\<rbrakk> \<Longrightarrow>
 taut p1 \<and>p p2 \<Rightarrow>p p1"
apply (utp_pred_taut_tac)
done

theorem
"\<lbrakk>p1 \<in> HO1_PREDICATE;
 p2 \<in> HO1_PREDICATE;
 \<alpha> p1 = \<alpha> p2\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<sqsubseteq> p1"
apply (simp)
apply (utp_pred_taut_tac)
done
end