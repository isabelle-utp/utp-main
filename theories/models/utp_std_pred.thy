(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/models/utp_std_pred.thy                                          *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Standard Predicates *}

theory utp_std_pred
imports "../GLOBAL" "../generic/utp_generic" utp_default_value
begin

text {* Standard predicates make use of composite default values. *}

type_synonym STD_VALUE = "DEFAULT_VALUE COMPOSITE_VALUE"
type_synonym STD_TYPE = "DEFAULT_TYPE COMPOSITE_TYPE"

subsection {* Locale @{term STD_PRED} *}

locale STD_PRED =
  COMPOSITE_VALUE "default_type_rel" +
  GEN_PRED "lift_type_rel_composite default_type_rel"
for default_type_rel :: "'BASIC_VALUE :: BASIC_SORT \<Rightarrow> 'BASIC_TYPE \<Rightarrow> bool"

subsection {* Locale Interpretation *}

interpretation STD : STD_PRED "default_type_rel"
apply (simp add: STD_PRED_def GEN_PRED_def)
apply (auto)
done

subsection {* Type Definitions *}

typedef (open) STD_PREDICATE = "STD.WF_ALPHA_PREDICATE"
  morphisms Dest_STD_PREDICATE Mk_STD_PREDICATE
apply (rule_tac x = "STD.FALSE" in exI)
apply (auto simp add:alpha_closure closure)
done

typedef (open) STD_ALPHABET = "STD.WF_ALPHABET"
  morphisms Dest_STD_ALPHABET Mk_STD_ALPHABET
apply (rule_tac x = "{}" in exI)
apply (auto simp add:alpha_closure)
done

text {* Default Simplifications *}

declare Mk_STD_PREDICATE_inverse [simp]
declare Mk_STD_PREDICATE_inject [simp, intro!]
declare Dest_STD_PREDICATE_inverse [simp]
(* declare Dest_STD_PREDICATE_inject [simp, intro!] *)
declare Dest_STD_PREDICATE [simp]

theorem Dest_STD_PREDICATE_inject_sym [simp, intro!] :
"(p1 = p2) \<longleftrightarrow> (Dest_STD_PREDICATE p1 = Dest_STD_PREDICATE p2)"
apply (simp add: Dest_STD_PREDICATE_inject)
done

declare Mk_STD_ALPHABET_inverse [simp]
declare Mk_STD_ALPHABET_inject [simp, intro!]
declare Dest_STD_ALPHABET_inverse [simp]
(* declare Dest_STD_ALPHABET_inject [simp, intro!] *)
declare Dest_STD_ALPHABET [simp]

theorem Dest_STD_ALPHABET_inject_sym [simp, intro!] :
"(p1 = p2) \<longleftrightarrow> (Dest_STD_PREDICATE p1 = Dest_STD_PREDICATE p2)"
apply (simp add: Dest_STD_ALPHABET_inject)
done

subsection {* Semantic Domains *}

definition STD_ALPHABET [simp] :
"STD_ALPHABET \<equiv> STD.WF_ALPHABET"

definition STD_BINDING [simp] :
"STD_BINDING \<equiv> STD.WF_BINDING"

definition STD_BINDING_SET [simp] :
"STD_BINDING_SET \<equiv> STD.WF_BINDING_SET"

definition STD_BINDING_FUN [simp] :
"STD_BINDING_FUN \<equiv> STD.WF_BINDING_FUN"

definition STD_PREDICATE [simp] :
"STD_PREDICATE \<equiv> STD.WF_ALPHA_PREDICATE"

definition STD_FUNCTION [simp] :
"STD_FUNCTION \<equiv> STD.WF_ALPHA_FUNCTION"

subsection {* Global Syntax *}

text {* Value Syntax *}

defs STD_type_rel [simp] :
"GLOBAL0.type_rel \<equiv> lift_type_rel_composite default_type_rel"

defs STD_set_type_rel [simp] :
"GLOBAL0.set_type_rel \<equiv> STD.set_type_rel"

text {* Predicate Syntax *}

definition STD_alphabet ::
  "STD_PREDICATE \<Rightarrow> STD_TYPE ALPHABET" ("\<alpha>") where
"\<alpha> p \<equiv> STD.alphabet (Dest_STD_PREDICATE p)"

definition STD_bindings ::
  "STD_PREDICATE \<Rightarrow>
   (STD_VALUE, STD_TYPE) BINDING_SET" ("\<beta>") where
"\<beta> p \<equiv> STD.bindings (Dest_STD_PREDICATE p)"

declare STD_alphabet_def [simp]
declare STD_bindings_def [simp]

(*
defs STD_beta_equiv [simp] :
"GLOBAL1.beta_equiv \<equiv> STD.beta_equiv"
*)

defs STD_LiftP [simp] :
"GLOBAL1.LiftP a bfun \<equiv>
 Mk_STD_PREDICATE (STD.LiftP a bfun)"

defs STD_TrueP [simp] :
"GLOBAL1.TrueP a \<equiv>
 Mk_STD_PREDICATE (STD.TrueP a)"

defs STD_FalseP [simp] :
"GLOBAL1.FalseP a \<equiv>
 Mk_STD_PREDICATE (STD.FalseP a)"

defs STD_TRUE [simp] :
"GLOBAL1.TRUE \<equiv>
 Mk_STD_PREDICATE STD.TRUE"

defs STD_FALSE [simp] :
"GLOBAL1.FALSE \<equiv>
 Mk_STD_PREDICATE STD.FALSE"

defs STD_ExtP [simp] :
"GLOBAL1.ExtP p a \<equiv>
 Mk_STD_PREDICATE
   (STD.ExtP (Dest_STD_PREDICATE p) a)"

defs STD_ResP [simp] :
"GLOBAL1.ResP p a\<equiv>
 Mk_STD_PREDICATE
   (STD.ResP (Dest_STD_PREDICATE p) a)"

defs STD_NotP [simp] :
"GLOBAL1.NotP p \<equiv>
 Mk_STD_PREDICATE
   (STD.NotP (Dest_STD_PREDICATE p))"

defs STD_AndP [simp] :
"GLOBAL1.AndP p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.AndP
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_OrP [simp] :
"GLOBAL1.OrP p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.OrP
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_ImpliesP [simp] :
"GLOBAL1.ImpliesP p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.ImpliesP
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_IffP [simp] :
"GLOBAL1.IffP p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.IffP
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_ExistsResP [simp] :
"GLOBAL1.ExistsResP a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ExistsResP a (Dest_STD_PREDICATE p))"

defs STD_ForallResP [simp] :
"GLOBAL1.ForallResP a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ForallResP a (Dest_STD_PREDICATE p))"

defs STD_ExistsP [simp] :
"GLOBAL1.ExistsP a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ExistsP a (Dest_STD_PREDICATE p))"

defs STD_ForallP [simp] :
"GLOBAL1.ForallP a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ForallP a (Dest_STD_PREDICATE p))"

defs STD_ClosureP [simp] :
"GLOBAL1.ClosureP p \<equiv>
 Mk_STD_PREDICATE
   (STD.ClosureP (Dest_STD_PREDICATE p))"

defs STD_RefP [simp] :
"GLOBAL1.RefP p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.RefP
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_Tautology [simp] :
"GLOBAL1.Tautology p \<equiv>
 STD.Tautology (Dest_STD_PREDICATE p)"

defs STD_Contradiction [simp] :
"GLOBAL1.Contradiction p \<equiv>
 STD.Contradiction (Dest_STD_PREDICATE p)"

defs STD_Contingency [simp] :
"GLOBAL1.Contingency p \<equiv>
 STD.Contingency (Dest_STD_PREDICATE p)"

defs STD_Refinement [simp] :
"GLOBAL1.Refinement p1 p2 \<equiv>
 STD.Refinement
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2)"

subsection {* Proof Experiments *}

theorem
"STD.MkInt(1) +v STD.MkInt(2) = STD.MkInt(3)"
apply (simp)
done

theorem
"STD.MkInt(1) \<in>v STD.MkSet({STD.MkInt(1), STD.MkInt(2)})"
apply (simp)
done

theorem
"STD.MkInt(3) \<in>v
 STD.MkSet({STD.MkInt(1)}) \<union>v STD.MkSet({STD.MkInt(1) +v STD.MkInt(2)})"
apply (simp)
done

theorem
"(p1 :: STD_PREDICATE) \<and>p (p2 \<and>p p3) = (p1 \<and>p p2) \<and>p p3"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem
"taut (p1 :: STD_PREDICATE) \<and>p p2 \<Rightarrow>p p1"
apply (utp_pred_taut_tac)
done

theorem
"\<alpha> (p1 :: STD_PREDICATE) = \<alpha> p2 \<Longrightarrow>
 p1 \<or>p p2 \<sqsubseteq> p1"
apply (simp)
apply (utp_pred_taut_tac)
done

theorem
"\<lbrakk>(\<alpha> (p1 :: STD_PREDICATE)) = (\<alpha> p2);
 taut (p1 \<Rightarrow>p p2)\<rbrakk> \<Longrightarrow>
 p1 = (p1 \<and>p p2)"
apply (utp_pred_taut_tac)
apply (auto)
done

theorem
"\<lbrakk>(\<alpha> (p1 :: STD_PREDICATE)) = (\<alpha> p2);
 taut (p1 \<Rightarrow>p p2)\<rbrakk> \<Longrightarrow>
 p1 = (p1 \<and>p p2)"
apply (utp_pred_taut_tac)
apply (auto intro: STD.AndP_intro)
done
end
