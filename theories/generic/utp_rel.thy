(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_rel.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Relations *}

theory utp_rel
imports utp_pred utp_eval utp_subst
begin

subsection {* Type Synonyms *}

type_synonym ('VALUE, 'TYPE) RELATION =
  "(('VALUE, 'TYPE) BINDING \<times> ('VALUE, 'TYPE) BINDING) set"

context PRED
begin

subsection {* Sequential Composition *}

definition OTHER_VAR :: "'TYPE VAR set" where
"OTHER_VAR = VAR - (DASHED \<union> UNDASHED)"

definition COMPOSABLE :: "('VALUE, 'TYPE) RELATION" where
"COMPOSABLE = {(b1, b2) .
   (\<forall> v \<in> UNDASHED . b1(dash v) = b2 v) \<and> b1 \<cong> b2 on OTHER_VAR}"

definition SS :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS = (\<lambda> v .
   if v \<in> UNDASHED then (dash v) else
   if v \<in> DASHED then (undash v) else v)"

definition SemiR ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 SemiR p1 p2 = {b1 \<oplus> b2 on DASHED | b1 b2 .
   b1 \<in> p1 \<and> b2 \<in> p2 \<and> (b1, b2) \<in> COMPOSABLE}"

(* Not sure about the precedence of sequential composition yet. *)

notation SemiR (infixr ";" 140)

subsection {* Evaluation Function *}

definition BindR ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) RELATION" where
"BindR b =
 {(rb1, rb2) . \<exists> b' \<in> WF_BINDING .
   rb1 = b \<oplus> b' on DASHED \<and> rb2 = (SubstB SS b) \<oplus> b' on DASHED}"

definition EvalR ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) RELATION" ("\<lbrakk>_\<rbrakk>R") where
"EvalR p = \<Union> (BindR ` p)"

definition IEvalR ::
  "('VALUE, 'TYPE) RELATION \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"IEvalR rbs =
 {rb1 \<oplus> (SubstB SS rb2) on DASHED | rb1 rb2 . (rb1, rb2) \<in> rbs}"

subsection {* Theorems *}

subsubsection {* Theorems about @{term SS} *}

text {* TODO: Maybe try and shorten the following proof. *}

theorem SS_VAR_SUBST [closure] :
"SS \<in> VAR_SUBST"
apply (simp add: SS_def VAR_SUBST_def)
apply (simp add: bij_def)
apply (rule conjI)
apply (simp add: inj_on_def)
apply (safe)
apply (auto)
apply (insert dash_inj undash_inj_on_DASHED)
-- {* Subgoal 1 *}
apply (simp add: inj_on_eq_iff)
-- {* Subgoal 2 *}
apply (simp add: inj_eq)
-- {* Subgoal 3 *}
apply (simp add: image_def)
apply (drule_tac x = "dash x" in bspec) back
apply (simp add: var_defs)
apply (simp)
-- {* Subgoal 4 *}
apply (simp add: image_def)
apply (drule_tac x = "undash x" in bspec)
apply (simp)
apply (simp)
done

theorem SS_VAR_SUBST_ON [closure] :
"SS \<in> VAR_SUBST_ON (UNDASHED \<union> DASHED)"
apply (simp add: VAR_SUBST_ON_def)
apply (simp add: SS_VAR_SUBST)
apply (simp add: SS_def)
done

theorem SS_VAR_SUBST_INV [closure] :
"SS \<in> VAR_SUBST_INV"
apply (simp add: VAR_SUBST_INV_def)
apply (simp add: SS_VAR_SUBST)
apply (rule sym [OF inv_equality])
apply (simp_all add: SS_def)
apply (auto)
done

theorem SS_inv [simp] :
"inv SS = SS"
apply (insert SS_VAR_SUBST_INV)
apply (simp add: VAR_SUBST_INV_def)
done

subsubsection {* Closure Theorems *}

theorem SemiR_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 ; p2 \<in> WF_PREDICATE"
apply (simp add: SemiR_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

subsubsection {* Transfer Theorems *}

lemma SS_DASHED_member :
"x \<in> DASHED \<Longrightarrow> \<not> SS x \<in> DASHED"
apply (simp add: SS_def)
apply (simp add: var_defs)
done

lemma IEvalR_inverse_lemma1 :
"\<lbrakk>b \<in> WF_BINDING;
 b' \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b \<oplus> SubstB SS (SubstB SS b \<oplus> b' on DASHED) on DASHED = b"
apply (rule ext)
apply (case_tac "x \<in> DASHED")
apply (simp_all add: SubstB_def SS_DASHED_member closure)
done

lemma IEvalR_inverse_lemma2 :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b \<oplus> SubstB SS (SubstB SS b \<oplus> b on DASHED) on DASHED = b"
apply (rule ext)
apply (case_tac "x \<in> DASHED")
apply (simp_all add: SubstB_def SS_DASHED_member closure)
done

theorem IEvalR_inverse :
"p \<in> WF_PREDICATE \<Longrightarrow> IEvalR (EvalR p) = p"
apply (simp add: IEvalR_def EvalR_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rename_tac bx rb1 rb2 b)
apply (simp add: BindR_def)
apply (clarsimp)
apply (simp add: IEvalR_inverse_lemma1)
-- {* Subgoal 2 *}
apply (rename_tac b)
apply (rule_tac x = "b" in exI)
apply (rule_tac x = "(SubstB SS b) \<oplus> b on DASHED" in exI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (simp add: IEvalR_inverse_lemma2)
-- {* Subgoal 2.2 *}
apply (rule_tac x = "b" in bexI)
apply (simp add: BindR_def)
apply (rule_tac x = "b" in bexI)
apply (simp_all)
done

theorem EvalR_inj :
"inj_on EvalR WF_PREDICATE"
apply (insert IEvalR_inverse)
apply (erule inj_on_inverseI)
done

theorem EvalR_simp :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 = p2 \<longleftrightarrow> \<lbrakk>p1\<rbrakk>R = \<lbrakk>p2\<rbrakk>R"
apply (rule inj_on_eval_simp [of EvalR WF_PREDICATE "p1" "p2"])
apply (simp add: EvalR_inj)
apply (assumption)+
done

theorem EvalR_intro :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 \<lbrakk>p1\<rbrakk>R = \<lbrakk>p2\<rbrakk>R\<rbrakk> \<Longrightarrow> p1 = p2"
apply (rule inj_on_eval_intro [of EvalR WF_PREDICATE "p1" "p2"])
apply (simp add: EvalR_inj)
apply (assumption)+
done

subsubsection {* Evaluation Theorems *}

theorem BindR_WF_BINDING_eq :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 rb \<in> BindR b1;
 rb \<in> BindR b2\<rbrakk> \<Longrightarrow> b1 = b2"
apply (simp add: BindR_def)
apply (safe)
apply (rename_tac x y b2' b1')
apply (simp add: override_on_equals)
apply (safe)
apply (rule ext)
apply (case_tac "x \<notin> DASHED")
-- {* Subgoal 1 *}
apply (simp)
-- {* Subgoal 2 *}
apply (clarsimp)
apply (drule_tac x = "undash x" in spec)
apply (subgoal_tac "undash x \<notin> DASHED")
apply (simp)
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (simp add: var_defs)
done

theorem EvalR_NotP :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<not>p p\<rbrakk>R = \<lbrakk>true\<rbrakk>R - \<lbrakk>p\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: NotP_def TrueP_def)
apply (auto)
apply (rename_tac rb b2 b1)
apply (subgoal_tac "b1 = b2")
apply (simp)
apply (simp add: BindR_WF_BINDING_eq closure)
done

theorem EvalR_AndP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<and>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<inter> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: AndP_def)
apply (auto)
apply (rename_tac b b1 b2)
apply (rule_tac x = "b2" in bexI)
apply (assumption)
apply (subgoal_tac "b1 = b2")
apply (simp)
apply (simp add: BindR_WF_BINDING_eq closure)
done

theorem EvalR_OrP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<or>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<union> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: OrP_def)
done

theorem SubstB_SS_COMPOSABLE_1 :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (b1, b2) \<in> COMPOSABLE; x \<notin> DASHED\<rbrakk> \<Longrightarrow>
 SubstB SS b1 x = b2 x"
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (safe)
apply (simp add: COMPOSABLE_def)
apply (simp add: COMPOSABLE_def)
apply (clarify)
apply (simp add: binding_equiv_def)
apply (simp add: OTHER_VAR_def)
apply (drule_tac x = "x" in bspec) back
apply (simp add: VAR_def)
apply (assumption)
done

theorem SubstB_SS_COMPOSABLE_2 :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (b1, b2) \<in> COMPOSABLE; x \<notin> DASHED\<rbrakk> \<Longrightarrow>
 SubstB SS (b1 \<oplus> b2 on DASHED) x = SubstB SS b2 x"
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (simp add: COMPOSABLE_def)
apply (clarify)
apply (simp add: binding_equiv_def)
apply (simp add: OTHER_VAR_def)
apply (drule_tac x = "x" in bspec) back
apply (simp add: VAR_def)
apply (assumption)
done

theorems SubstB_SS_COMPOSABLE =
  SubstB_SS_COMPOSABLE_1
  SubstB_SS_COMPOSABLE_2

theorem BindR_COMPOSABLE :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (rb1, rb3) \<in> BindR b1;
 (rb3, rb2) \<in> BindR b2\<rbrakk> \<Longrightarrow>
 (b1, b2) \<in> COMPOSABLE"
apply (simp add: BindR_def COMPOSABLE_def)
apply (safe)
apply (simp_all add: SubstB_def closure)
apply (simp_all add: override_on_equals)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: SS_def)
apply (drule_tac x = "v" in spec) back
apply (simp)
apply (subgoal_tac "v \<notin> DASHED")
apply (simp)
apply (auto) [1]
-- {* Subgoal 2 *}
apply (simp add: binding_equiv_def)
apply (simp add: OTHER_VAR_def)
apply (safe)
apply (simp add: SS_def)
apply (drule_tac x = "x" in spec) back
apply (simp)
done

theorem BindR_override :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (rb1, rb3) \<in> BindR b1;
 (rb3, rb2) \<in> BindR b2\<rbrakk> \<Longrightarrow>
 (rb1, rb2) \<in> BindR (b1 \<oplus> b2 on DASHED)"
apply (frule BindR_COMPOSABLE [of b1 b2 rb1 rb3 rb2])
apply (assumption)+
apply (simp add: BindR_def)
apply (safe)
apply (rule_tac x = "b'a" in bexI)
apply (simp add: override_on_equals)
apply (clarify)
apply (drule_tac x = "x" in spec) back
apply (clarify)
apply (simp add: SubstB_SS_COMPOSABLE_2)
apply (assumption)
done

theorem EvalR_SemiR :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 ; p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R O \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: SemiR_def)
apply (simp add: rel_comp_def)
apply (insert WF_BINDING_exists)
apply (safe)
-- {* Subgoal 1 *}
apply (simp_all)
apply (rename_tac rb1 rb2 b1 b2)
apply (rule_tac x = "(SubstB SS b1) \<oplus> rb1 on DASHED" in exI)
apply (rule conjI)
-- {* Subgoal 1.1 *}
apply (rule_tac x = "b1" in bexI)
apply (simp add: BindR_def)
apply (clarify)
apply (rule_tac x = "b'" in bexI)
apply (simp)
apply (assumption)+
-- {* Subgoal 1.2 *}
apply (rule_tac x = "b2" in bexI)
apply (simp add: BindR_def)
apply (clarify)
apply (rule_tac x = "b'" in bexI)
apply (simp add: override_on_equals)
apply (simp add: SubstB_SS_COMPOSABLE)
apply (assumption)+
-- {* Subgoal 2 *}
apply (rename_tac rb1 rb2 rb3 b1 b2)
apply (rule_tac x = "b1 \<oplus> b2 on DASHED" in exI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (rule_tac x = "b1" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (simp add: BindR_COMPOSABLE)
-- {* Subgoal 2.1 *}
apply (simp add: BindR_override)
done

subsection {* Proof Experiments *}

theorem SemiP_assoc :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (p1 ; p2) ; p3 = p1 ; (p2 ; p3)"
apply (subgoal_tac "(p1 ; p2) \<in> WF_PREDICATE")
apply (subgoal_tac "(p2 ; p3) \<in> WF_PREDICATE")
apply (simp add: SemiR_def)
apply (safe)
(* This is still fairly nasty! *)
oops

theorem SemiP_assoc :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (p1 ; p2) ; p3 = p1 ; (p2 ; p3)"
apply (simp add: EvalR_simp closure)
apply (simp add: EvalR_SemiR closure)
apply (auto)
done

theorem SemiP_OrP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 ; (p2 \<or>p p3) = (p1 ; p2) \<or>p (p1 ; p3)"
apply (simp add: EvalR_simp closure)
apply (simp add: EvalR_SemiR EvalR_OrP closure)
done
end
end