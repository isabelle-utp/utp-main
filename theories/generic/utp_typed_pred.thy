(******************************************************************************)
(* Title: utp/generic/utp_typed_pred.thy                                      *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_typed_pred
imports utp_composite_value utp_gen_pred
begin

section {* Typed Predicates *}

subsection {* Well-typed Bindings *}

definition WT_BINDING :
"WT_BINDING type_rel = {b . (\<forall> v . type_rel (b v) (type v))}"

subsection {* Locale @{text TYPED_PRED} *}

locale TYPED_PRED = GEN_PRED "(WT_BINDING type_rel)"
for type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool"

subsection {* Theorems *}

theorem WT_BINDING_non_empty [intro!, simp] :
"VALUE type_rel \<Longrightarrow>
 WT_BINDING type_rel \<noteq> {}"
apply (simp add: WT_BINDING)
apply (rule_tac x = "(\<lambda> v . (SOME x . type_rel x (type v)))" in exI)
apply (clarify)
apply (drule_tac t = "snd v" in VALUE.type_non_empty)
apply (clarify)
apply (rule_tac a = "x" in someI2)
apply (assumption)+
done

theorem WT_BINDING_override [intro!, simp] :
"\<lbrakk>b1 \<in> WT_BINDING type_rel;
 b2 \<in> WT_BINDING type_rel\<rbrakk> \<Longrightarrow>
 (b1 \<oplus> b2 on a) \<in> WT_BINDING type_rel"
apply (simp add: WT_BINDING)
apply (clarify)
apply (case_tac "v \<in> a")
apply (auto)
done

text {* The following theorem facilitates locale instantiation. *}

theorem TYPED_PRED_inst [intro!, simp] :
"\<lbrakk>VALUE type_rel\<rbrakk> \<Longrightarrow> TYPED_PRED type_rel"
apply (simp add: TYPED_PRED_def)
apply (simp add: GEN_PRED_def)
done
end
