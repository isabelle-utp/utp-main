(******************************************************************************)
(* Title: utp/models/utp_ho2_pred.thy                                         *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho2_pred
imports "../GLOBAL" "../generic/utp_generic" "../utils/utp_ho2_utils"
  utp_ho2_value
begin

section {* HO2 Predicates *}

subsection {* Type Synonyms *}

text {* Maybe these should be introduced as part of the instantiation. *}

types STD_VAR = "STD_TYPE VAR"
types HO1_VAR = "HO1_TYPE VAR"
types HO2_VAR = "HO2_TYPE VAR"

types STD_BINDING = "(STD_VALUE, STD_TYPE) BINDING"
types HO1_BINDING = "(HO1_VALUE, HO1_TYPE) BINDING"
types HO2_BINDING = "(HO2_VALUE, HO2_TYPE) BINDING"

types STD_PREDICATE = "(STD_VALUE, STD_TYPE) ALPHA_PREDICATE"
types HO1_PREDICATE = "(HO1_VALUE, HO1_TYPE) ALPHA_PREDICATE"
types HO2_PREDICATE = "(HO2_VALUE, HO2_TYPE) ALPHA_PREDICATE"

subsection {* HO2 Bindings *}

definition HO2_CONSISTENT_1 :: "HO2_VAR \<Rightarrow> HO2_BINDING set" where
"(IsProg2Var m2) \<longrightarrow>
 HO2_CONSISTENT_1 m2 =
   {b2 . (\<forall> b1 \<in> \<beta> (call (b2 m2)) .
     (\<forall> m . (IsProgVar m) \<longrightarrow> b2 (m \<up>VAR) = (b1 m) \<up>VAL))}"

definition HO2_CONSISTENT_2 :: "HO2_VAR \<Rightarrow> HO2_VAR \<Rightarrow> HO2_BINDING set" where
"(IsProg1Var m1) \<and>
 (IsProg2Var m2) \<and>
 (var_name m1) = (var_name m2) \<longrightarrow>
 HO2_CONSISTENT_2 m1 m2 =
   {b2 . (\<forall> b1 \<in> \<beta> (call (b2 m2)) . (b1 \<down>BIND) \<in> \<beta> (call (b2 m1)))}"

definition HO2_CONSISTENT :: "HO2_BINDING set" where
"HO2_CONSISTENT =
   (\<Inter> {bs . (\<exists> m2 . (IsProg2Var m2) \<and> bs = HO2_CONSISTENT_1 m2)}) \<inter>
   (\<Inter> {bs . (\<exists> m1 m2 . (IsProg1Var m1) \<and> (IsProg2Var m2) \<and>
     (var_name m1) = (var_name m2) \<and> bs = HO2_CONSISTENT_2 m1 m2)})"

subsection {* Locale Instantiation *}

locale HO2_PRED =
  HO2_VALUE_LOCALE +
  GEN_PRED "(WT_BINDING ho2_type_rel) \<inter> HO2_CONSISTENT"

interpretation HO2 : HO2_PRED
apply (unfold HO2_PRED_def HO2_VALUE_LOCALE_def GEN_PRED_def)
apply (simp add: HO2_CONSISTENT_def)
apply (simp only: non_empty_exists)
apply (rule_tac x =
  "(\<lambda> v :: HO2_VAR .
     if (IsStdVar v) then
       (SOME x . ho2_type_rel x (type v))
     else
     if (IsProg1Var v) then
       Prog1Val (Mk_STD_PREDICATE
         (STD.FalseP (Dest_STD_ALPHABET (Prog1TypeOf (type v)))))
     else
     if (IsProg2Var v) then
       Prog2Val (Mk_HO1_PREDICATE
         (HO1.FalseP (Dest_HO1_ALPHABET (Prog2TypeOf (type v)))))
     else dont_care)" in exI)
apply (safe)
-- {* Goal 1 *}
apply (simp add: WT_BINDING)
apply (safe, auto dest: IsVar_dest)
-- {* Goal 1.1 *}
apply (drule IsProg2Var_exists_type)
apply (clarsimp)
-- {* Goal 1.2 *}
apply (drule IsProg1Var_exists_type)
apply (clarsimp)
-- {* Goal 1.3 *}
apply (drule IsStdVar_exists_type)
apply (clarsimp)
apply (rule someI2_ex)
apply (rule_tac x = "HO2_VALUE.BaseVal (SOME x . x : t)" in exI)
apply (simp)
apply (rule someI2_ex)
apply (simp add: STD.type_non_empty)
apply (assumption)+
-- {* Goal 2 *}
apply (simp add: HO2_CONSISTENT_1_def)
apply (auto dest: IsVar_dest)
-- {* Goal 2.1 *}
apply (simp add: Call_simps)
apply (simp add: HO1.FalseP_def)
-- {* Goal 2.2 *}
apply (simp add: Call_simps)
apply (simp add: HO1.FalseP_def)
-- {* Goal 2.3 *}
apply (simp add: Call_simps)
apply (simp add: HO1.FalseP_def)
-- {* Goal 3 *}
apply (simp add: HO2_CONSISTENT_2_def)
apply (auto dest: IsVar_dest)
apply (simp add: Call_simps)
apply (simp add: HO1.FalseP_def)
done

subsection {* Semantic Domains *}

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

text {* Should the following be done in the theory @{text utp_ho2_value}? *}

defs HO2_type_rel [simp] :
"GLOBAL.type_rel \<equiv> ho2_type_rel"

defs HO2_set_type_rel [simp] :
"GLOBAL.set_type_rel \<equiv> HO2.set_type_rel"

subsubsection {* Predicate Syntax *}

defs HO2_alphabet [simp] :
"GLOBAL.alphabet \<equiv> HO2.alphabet"

defs HO2_bindings [simp] :
"GLOBAL.bindings \<equiv> HO2.bindings"

defs HO2_binding_equiv [simp] :
"GLOBAL.binding_equiv \<equiv> HO2.binding_equiv"

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