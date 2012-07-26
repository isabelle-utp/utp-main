(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_pred.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Substitution *}

theory utp_subst
imports utp_pred utp_eval
begin

context PRED
begin

subsection {* Variable Substitutions *}

text {* Substitutions are total bijections and have to respect typing. *}

definition VAR_SUBST :: "('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST = {ss . bij ss \<and> (\<forall> v . type (ss v) = type v)}"

subsection {* Restrictions *}

text {* Variable substitutions confined to a set of variables. *}

definition VAR_SUBST_ON ::
  "('TYPE VAR) set \<Rightarrow> ('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST_ON vs = {ss . ss \<in> VAR_SUBST \<and> (\<forall> v . v \<notin> vs \<longrightarrow> ss v = v)}"

text {* Variable substitutions that are moreover involutions. *}

definition VAR_SUBST_INV :: "('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST_INV = {ss . ss \<in> VAR_SUBST \<and> ss = inv ss}"

subsection {* Binding Substitution *}

definition SubstB ::
  "('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING" where
"\<lbrakk>ss \<in> VAR_SUBST; b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b = b \<circ> (inv ss)"

subsection {* Predicate Substitution *}

definition SubstP ::
  " ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" ("_[_]" [200]) where
"\<lbrakk>ss \<in> VAR_SUBST; p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 SubstP p ss = (SubstB ss) ` p"

subsection {* Theorems *}

subsubsection {* Bijections *}

(* Should we have a corresponding theorem for variable substitution? *)

theorem bij_comp_inject [simp] :
"bij g \<Longrightarrow> (f1 \<circ> g = f2 \<circ> g) = (f1 = f2)"
apply (safe)
apply (rule ext)
apply (subgoal_tac "\<exists> y . x = g y")
apply (clarify)
apply (drule_tac x = "y" in fun_cong)
apply (auto)
apply (simp add: bij_def surj_def)
done

declare bij_imp_bij_inv [simp, intro!]

subsubsection {* Variable Substitution *}

text {* Theorems about @{term "VAR_SUBST"} *}

theorem VAR_SUBST_bij :
"ss \<in> VAR_SUBST \<Longrightarrow> bij ss"
apply (simp add: VAR_SUBST_def)
done

theorem VAR_SUBST_id [closure]:
"id \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
done

theorem VAR_SUBST_inv [closure] :
"ss \<in> VAR_SUBST \<Longrightarrow> (inv ss) \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (safe)
apply (drule_tac x = "inv ss v" in spec)
apply (erule subst)
apply (simp add: bij_def surj_f_inv_f)
done

theorem VAR_SUBST_compose [closure]:
"\<lbrakk>ss1 \<in> VAR_SUBST;
 ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 ss1 \<circ> ss2 \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (clarify)
apply (simp add: bij_comp)
done

theorem VAR_SUBST_WF_BINDING [closure] :
"\<lbrakk>b \<in> WF_BINDING;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 b \<circ> ss \<in> WF_BINDING"
apply (simp add: VAR_SUBST_def WF_BINDING_def)
apply (safe)
apply (drule_tac x = "ss v" in spec)
apply (drule_tac x = "v" in spec)
apply (auto)
done

theorem VAR_SUBST_inject [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> (f1 \<circ> ss = f2 \<circ> ss) = (f1 = f2)"
apply (drule VAR_SUBST_bij)
apply (simp)
done

theorem VAR_SUBST_inv_inv [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> inv (inv ss) = ss"
apply (simp add: VAR_SUBST_def)
apply (simp add: inv_inv_eq)
done

theorem VAR_SUBST_ss_inv_app [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> ss (inv ss x) = x"
apply (simp add: VAR_SUBST_def)
apply (simp add: surj_f_inv_f bij_def)
done

theorem VAR_SUBST_inv_ss_app [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> inv ss (ss x) = x"
apply (simp add: VAR_SUBST_def)
apply (simp add: inv_f_f bij_def)
done

theorem VAR_SUBST_image_inv [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> ss ` (inv ss) ` a = a"
apply (simp add: image_def)
apply (auto)
done

theorem VAR_SUBST_inv_image [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> (inv ss) ` ss ` a = a"
apply (simp add: image_def)
apply (auto)
done

theorem VAR_SUBST_in_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow> ss x \<in> (ss ` a) = (x \<in> a)"
apply (simp add: VAR_SUBST_def)
apply (auto simp: bij_def inj_eq)
done

text {* Theorems about @{term "VAR_SUBST_ON"} *}

theorem VAR_SUBST_ON_bij :
"ss \<in> VAR_SUBST_ON vs \<Longrightarrow> bij ss"
apply (simp add: VAR_SUBST_ON_def VAR_SUBST_def)
done

theorem VAR_SUBST_ON_VAR_SUBST [closure] :
"ss \<in> VAR_SUBST_ON vs \<Longrightarrow> ss \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_ON_def)
done

theorem VAR_SUBST_ON_id [closure]:
"id \<in> VAR_SUBST_ON vs"
apply (simp add: VAR_SUBST_ON_def VAR_SUBST_id)
done

theorem VAR_SUBST_ON_inv [closure] :
"ss \<in> VAR_SUBST_ON vs \<Longrightarrow>
 (inv ss) \<in> VAR_SUBST_ON vs"
apply (simp add: VAR_SUBST_ON_def)
apply (safe)
apply (simp add: VAR_SUBST_inv)
apply (drule_tac x = "v" in spec)
apply (clarify)
apply (drule sym)
apply (erule ssubst)
back back
apply (simp)
done

(* Should the following three theorems be default simplifications? *)
  
(* This causes a loop though when simplifying VAR_SUBST_ON. *)

theorem VAR_SUBST_ON_app_simp :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> ss x = x"
apply (simp add: VAR_SUBST_ON_def)
done

theorem VAR_SUBST_ON_app_member :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<in> vs\<rbrakk> \<Longrightarrow> ss x \<in> vs"
apply (simp only: VAR_SUBST_ON_def)
apply (clarify)
apply (drule VAR_SUBST_bij)
apply (simp add: bij_def)
apply (clarify)
apply (case_tac "ss x \<in> vs")
apply (assumption)
apply (drule_tac x = "ss x" in spec)
apply (clarify)
apply (subgoal_tac "ss x = x")
apply (auto dest: injD)
done

theorem VAR_SUBST_ON_app_not_member :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> ss x \<notin> vs"
apply (simp only: VAR_SUBST_ON_def)
apply (clarify)
apply (drule VAR_SUBST_bij)
apply (simp add: bij_def)
done

theorem VAR_SUBST_ON_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1\<rbrakk> \<Longrightarrow>
 ss ` vs1 = vs1"
apply (simp add: image_def)
apply (safe)
apply (simp add: VAR_SUBST_ON_app_member)
apply (rule_tac x = "inv ss x" in bexI)
apply (simp add: VAR_SUBST_ON_VAR_SUBST)
apply (subgoal_tac "ss x \<in> vs1")
apply (drule VAR_SUBST_ON_inv)
apply (simp add: VAR_SUBST_ON_app_member)
apply (simp add: VAR_SUBST_ON_app_member)
done

theorem VAR_SUBST_ON_disj_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss ` vs2 = vs2"
apply (simp add: VAR_SUBST_ON_def)
apply (clarify)
apply (simp add: image_def)
apply (safe)
apply (auto) [1]
apply (rule_tac x = "x" in bexI)
apply (auto)
done

theorem VAR_SUBST_ON_disj_comm :
"\<lbrakk>ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss1 \<circ> ss2 = ss2 \<circ> ss1"
apply (rule ext)
apply (simp)
apply (case_tac "x \<notin> vs1")
apply (simp add: VAR_SUBST_ON_app_simp)
apply (case_tac "x \<in> vs2")
apply (subgoal_tac "ss2 x \<notin> vs1")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "ss2 x \<in> vs2")
apply (auto) [1]
apply (simp add: VAR_SUBST_ON_app_member)
apply (case_tac "x \<notin> vs2")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "ss1 x \<notin> vs2")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "ss1 x \<in> vs1")
apply (auto) [1]
apply (simp add: VAR_SUBST_ON_app_member)
apply (auto)
done

text {* Theorems about @{term "VAR_SUBST_INV"} *}

theorem VAR_SUBST_INV_bij :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> bij ss"
apply (simp add: VAR_SUBST_INV_def VAR_SUBST_def)
done

theorem VAR_SUBST_INV_inv :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> ss = inv ss"
apply (simp add: VAR_SUBST_INV_def)
done

theorem VAR_SUBST_INV_VAR_SUBST [closure] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> ss \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_INV_def)
done

text {* Binding Substitution *}

theorem SubstB_closure [closure] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b \<in> WF_BINDING"
apply (simp add: SubstB_def closure)
done

theorem SubstsB_inject [simp]:
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (SubstB ss b1 = SubstB ss b2) = (b1 = b2)"
apply (simp add: SubstB_def)
apply (simp add: VAR_SUBST_def)
done

theorem SubstB_id [simp] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB id b = b"
apply (simp add: SubstB_def closure)
done

theorem SubstB_compose :
"\<lbrakk>ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss1 (SubstB ss2 b) = SubstB (ss1 \<circ> ss2) b"
apply (subgoal_tac "SubstB ss2 b \<in> WF_BINDING")
apply (simp add: SubstB_def closure)
apply (simp add: o_inv_distrib o_assoc VAR_SUBST_def)
apply (simp add: closure)
done

theorem SubstB_disj_comm :
"\<lbrakk>ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {};
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss1 (SubstB ss2 b) = SubstB ss2 (SubstB ss1 b)"
apply (simp add: SubstB_compose VAR_SUBST_ON_VAR_SUBST)
apply (subgoal_tac "ss1 \<circ> ss2 = ss2 \<circ> ss1")
apply (simp)
apply (auto intro: VAR_SUBST_ON_disj_comm)
done

theorem SubstB_inv_cancel1 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB (inv ss) (SubstB ss b) = b"
apply (subgoal_tac "SubstB ss b \<in> WF_BINDING")
apply (simp add: SubstB_def closure)
apply (rule ext)
apply (simp_all add: closure)
done

theorem SubstB_inv_cancel2 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (SubstB (inv ss) b) = b"
apply (subgoal_tac "SubstB (inv ss) b \<in> WF_BINDING")
apply (simp add: SubstB_def closure)
apply (rule ext)
apply (simp_all add: closure)
done

(* Maybe rename the following four distribution theorems. *)

theorem SubstB_override_distr1 :
"\<lbrakk>ss \<in> VAR_SUBST;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (b1 \<oplus> b2 on vs) = (SubstB ss b1) \<oplus> (SubstB ss b2) on (ss ` vs)"
apply (simp add: SubstB_def closure)
apply (simp add: override_on_def)
apply (rule ext)
apply (clarsimp)
apply (safe)
apply (subgoal_tac "a = ss (inv ss a)")
apply (simp_all)
done

theorem SubstB_override_distr2 :
"\<lbrakk>ss \<in> VAR_SUBST;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 (SubstB ss b1) \<oplus> (SubstB ss b2) on (ss ` vs) = SubstB ss (b1 \<oplus> b2 on vs)"
apply (simp add: SubstB_override_distr1)
done

theorem SubstB_override_distr3 :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 SubstB ss (b1 \<oplus> b2 on vs2) = (SubstB ss b1) \<oplus> (SubstB ss b2) on vs2"
apply (subst SubstB_override_distr1 [of ss b1 b2 vs2]);
apply (simp_all add: closure)
done

theorem SubstB_override_distr4 :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (SubstB ss b1) \<oplus> (SubstB ss b2) on vs2 = SubstB ss (b1 \<oplus> b2 on vs2)"
apply (simp add: SubstB_override_distr3)
done

theorem SubstB_involution [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_INV;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (SubstB ss b) = b"
apply (subgoal_tac "ss \<circ> ss = id")
apply (drule VAR_SUBST_INV_VAR_SUBST)
apply (simp add: SubstB_compose)
apply (simp add: VAR_SUBST_INV_def)
apply (clarify)
apply (erule ssubst) back
apply (simp)
done

subsubsection {* Predicate Substitution *}

(* The following theorem does not seem to be used. Maybe remove it! *)

lemma SubstP_closure_lemma :
"\<lbrakk>ss \<in> VAR_SUBST;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 (SubstB ss b1) \<cong> b2 on (ss ` a) \<longrightarrow>
 b1 \<cong> (SubstB (inv ss) b2) on a"
apply (simp add: binding_equiv_def)
apply (simp add: SubstB_def closure)
done

theorem SubstP_closure [closure] :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss] \<in> WF_PREDICATE"
apply (simp add: SubstP_def)
apply (simp add: WF_PREDICATE_def)
apply (safe)
apply (subgoal_tac "xa \<in> WF_BINDING")
apply (simp add: closure)
apply (auto)
done

theorem EvalP_SubstP [eval] :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>p[ss]\<rbrakk>b = \<lbrakk>p\<rbrakk>(SubstB (inv ss) b)"
apply (simp add: EvalP_def)
apply (simp add: SubstP_def)
apply (simp add: image_def)
apply (safe)
apply (simp)
apply (rule_tac x = "SubstB (inv ss) b" in bexI)
apply (simp)
apply (assumption)
done

theorem EvalP_SubstsP_SubstB [simp] :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 \<lbrakk>p[ss]\<rbrakk>(SubstB ss b) = \<lbrakk>p\<rbrakk>b"
apply (simp add: EvalP_def)
apply (simp add: SubstP_def)
apply (simp add: image_def)
done

subsubsection {* Algebraic Laws *}

theorem SubstP_inverse :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss][inv ss] = p"
apply (utp_pred_tac)
done

theorem SubstP_compose :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss1 \<in> VAR_SUBST;
 ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss1][ss2] = p[ss2 \<circ> ss1]"
apply (utp_pred_tac)
apply (clarify)
apply (simp add: SubstB_compose closure)
apply (drule VAR_SUBST_bij)+
apply (simp add: o_inv_distrib)
done

theorem SubstP_disj_comm:
"\<lbrakk>p \<in> WF_PREDICATE;
 ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 p[ss1][ss2] = p[ss2][ss1]"
apply (utp_pred_tac)
apply (clarify)
apply (subst SubstB_disj_comm [of "(inv ss1)" "vs1" "(inv ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

theorem SubstP_id :
"p \<in> WF_PREDICATE \<Longrightarrow> p[id] = p"
apply (utp_pred_tac)
done

theorem SubstP_NotP_distr :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (\<not>p p)[ss] = \<not>p p[ss]"
apply (utp_pred_tac)
done

theorem SubstP_AndP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<and>p p2)[ss] = p1[ss] \<and>p p2[ss]"
apply (utp_pred_tac)
done

theorem SubstP_OrP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<or>p p2)[ss] = p1[ss] \<or>p p2[ss]"
apply (utp_pred_tac)
done

theorem SubstP_ImpliesP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<Rightarrow>p p2)[ss] = p1[ss] \<Rightarrow>p p2[ss]"
apply (utp_pred_tac)
done

theorem SubstP_IffP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<Leftrightarrow>p p2)[ss] = p1[ss] \<Leftrightarrow>p p2[ss]"
apply (utp_pred_tac)
done

theorem SubstP_ExistsP_distr :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<exists>p vs2 . p)[ss] = (\<exists>p vs2 . p[ss])"
apply (utp_pred_tac)
apply (safe)
apply (subgoal_tac "(inv ss) \<in> VAR_SUBST_ON vs1")
apply (rule_tac x = "SubstB ss b'" in bexI)
apply (subst SubstB_override_distr3 [of "(inv ss)" vs1])
apply (simp_all add: closure)
apply (subgoal_tac "(inv ss) \<in> VAR_SUBST_ON vs1")
apply (rule_tac x = "SubstB (inv ss) b'" in bexI)
apply (subst SubstB_override_distr4 [of "(inv ss)" vs1])
apply (simp_all add: closure)
done

theorem SubstP_ForallP_distr :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<forall>p vs2 . p)[ss] = (\<forall>p vs2 . p[ss])"
apply (simp add: ForallP_def closure)
apply (simp add: SubstP_ExistsP_distr SubstP_NotP_distr closure)
done

theorem SubstP_ClosureP :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 [p[ss]] = ([p] :: ('VALUE, 'TYPE) PREDICATE)"
apply (utp_pred_tac)
apply (safe)
apply (drule_tac x = "SubstB ss x" in bspec)
apply (simp_all add: closure)
done

subsection {* Proof Experiments *}

text {*
  The following proof illustrate how we use a mixture of algebraic laws and
  the proof strategy for predicates to proof more complex properties. For now
  the strategy alone is not powerful enough to prove the theorem by itself.
*}

theorem SubstP_lemma1 :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 taut [p1 \<Leftrightarrow>p p2] \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]"
apply (utp_pred_tac)
apply (auto simp add: closure)
oops

theorem SubstP_lemma1 :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 taut [p1 \<Leftrightarrow>p p2] \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]"
apply (subgoal_tac "p1[ss] \<Leftrightarrow>p p2[ss] = (p1 \<Leftrightarrow>p p2)[ss]")
apply (simp)
apply (simp add: SubstP_ClosureP closure)
apply (utp_pred_tac)
apply (simp add: SubstP_IffP_distr)
done
end
end