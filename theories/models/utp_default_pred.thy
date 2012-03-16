theory utp_default_pred
imports "../GLOBAL" "../generic/utp_typed_pred" utp_default_values
begin

section {* Default Predicates *}

subsection {* Type Synonyms *}

types STD_VALUE = "DEFAULT_VALUE COMPLEX_VALUE"
types STD_TYPE = "DEFAULT_TYPE COMPLEX_TYPE"
types STD_VAR = "DEFAULT_TYPE COMPLEX_TYPE VAR"
types STD_ALPHABET = "STD_VAR ALPHABET"
types STD_BINDING = "(STD_VAR, STD_VALUE) BINDING"
types STD_BINDING_SET = "(STD_VAR, STD_VALUE) BINDING_SET"
types STD_BINDING_FUN = "(STD_VAR, STD_VALUE) BINDING_FUN"
types STD_PREDICATE = "(STD_VAR, STD_VALUE) ALPHA_PREDICATE"
types STD_FUNCTION = "(STD_VAR, STD_VALUE) ALPHA_FUNCTION"

subsection {* Interpretation *}

interpretation STD :
  TYPED_PRED "default_type_rel" "default_value_ref"
apply (auto)
done

subsection {* Definitions *}

definition STD_ALPHABET [simp] :
"STD_ALPHABET \<equiv> STD.WF_ALPHABET"

definition STD_BINDING [simp] :
"STD_BINDING \<equiv> WT_BINDING default_type_rel"

definition STD_BINDING_SET [simp] :
"STD_BINDING_SET \<equiv> STD.WF_BINDING_SET"

definition STD_BINDING_FUN [simp] :
"STD_BINDING_FUN \<equiv> STD.WF_BINDING_FUN"

definition STD_PREDICATE [simp] :
"STD_PREDICATE \<equiv> STD.WF_ALPHA_PREDICATE"

subsection {* Global Syntax *}

defs STD_BINDING_EQUIV [simp] :
"GLOBAL.BINDING_EQUIV \<equiv> STD.BINDING_EQUIV"

defs STD_LiftP [simp] :
"GLOBAL.LiftP \<equiv> STD.LiftP"

defs STD_TrueP [simp] :
"GLOBAL.TrueP \<equiv> STD.TrueP"

defs STD_FalseP [simp] :
"GLOBAL.FalseP \<equiv> STD.FalseP"

defs STD_TRUE [simp] :
"GLOBAL.TRUE \<equiv> STD.TRUE"

defs STD_FALSE [simp] :
"GLOBAL.FALSE \<equiv> STD.FALSE"

defs STD_ExtP [simp] :
"GLOBAL.ExtP \<equiv> STD.ExtP"

defs STD_ResP [simp] :
"GLOBAL.ResP \<equiv> STD.ResP"

defs STD_NotP [simp] :
"GLOBAL.NotP \<equiv> STD.NotP"

defs STD_AndP [simp] :
"GLOBAL.AndP \<equiv> STD.AndP"

defs STD_OrP [simp] :
"GLOBAL.OrP \<equiv> STD.OrP"

defs STD_ImpliesP [simp] :
"GLOBAL.ImpliesP \<equiv> STD.ImpliesP"

defs STD_IffP [simp] :
"GLOBAL.IffP \<equiv> STD.IffP"

defs STD_ExistsP :
"GLOBAL.ExistsP \<equiv> STD.ExistsP"

defs STD_ForallP [simp] :
"GLOBAL.ForallP \<equiv> STD.ForallP"

defs STD_ExistsExtP [simp] :
"GLOBAL.ExistsExtP \<equiv> STD.ExistsExtP"

defs STD_ForallExtP [simp] :
"GLOBAL.ForallExtP \<equiv> STD.ForallExtP"

defs STD_ClosureP [simp] :
"GLOBAL.ClosureP \<equiv> STD.ClosureP"

defs STD_RefP [simp] :
"GLOBAL.RefP \<equiv> STD.RefP"

defs STD_Tautology [simp] :
"GLOBAL.Tautology \<equiv> STD.Tautology"

defs STD_Contradiction [simp] :
"GLOBAL.Contradiction \<equiv> STD.Contradiction"

defs STD_Refinement [simp] :
"GLOBAL.Refinement \<equiv> STD.Refinement"

subsection {* Proof Experiments *}

text {* Value Proofs *}

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

text {* Predicate Proofs *}

theorem
"\<lbrakk>p1 \<in> STD_PREDICATE;
 p2 \<in> STD_PREDICATE;
 p3 \<in> STD_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p (p2 \<and>p p3) = (p1 \<and>p p2) \<and>p p3"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem
"\<lbrakk>p1 \<in> STD_PREDICATE;
 p2 \<in> STD_PREDICATE\<rbrakk> \<Longrightarrow>
 taut p1 \<and>p p2 \<Rightarrow>p p1"
apply (utp_pred_taut_tac)
done

theorem
"\<lbrakk>p1 \<in> STD_PREDICATE;
 p2 \<in> STD_PREDICATE;
 \<alpha> p1 = \<alpha> p2\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<sqsubseteq> p1"
apply (simp)
apply (utp_pred_taut_tac)
done
end