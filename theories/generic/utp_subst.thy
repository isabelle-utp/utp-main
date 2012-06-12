(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/theories/utp_subst.thy                                           *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Substitution *}

theory utp_subst
imports utp_gen_pred utp_eval_tactic
begin

context GEN_PRED
begin

subsection {* Variable Substitutions *}

text {* Substitutions are total bijections and have to respect typing. *}

definition VAR_SUBST :: "('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST = {ss . bij ss \<and> (\<forall> v . type (ss v) = type v)}"

definition mappings :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where
"mappings f = {v. f v \<noteq> v} \<union> {v. (inv f) v \<noteq> v}"

lemma mappings_inv: "bij f \<Longrightarrow> mappings (inv f) = mappings f"
  by (auto simp add:mappings_def bij_def inv_inv_eq)

lemma disj_mapping_comm: "\<lbrakk> inj f; inj g; mappings f \<inter> mappings g = {} \<rbrakk> \<Longrightarrow> f \<circ> g = g \<circ> f"
  apply(auto simp add:mappings_def Int_def comp_def)
  apply(rule ext)
  apply(smt inv_f_f)
done

lemma disj_mapping_image: "\<lbrakk> mappings f \<inter> a = {} \<rbrakk> \<Longrightarrow> f ` a = a"
  apply(auto simp add:mappings_def Un_def Int_def image_def)
  apply(metis)+
done

subsection {* Binding Substitution *}

definition SubstB ::
  "('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING" where
"\<lbrakk>ss \<in> VAR_SUBST; b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b = b \<circ> (inv ss)"

subsection {* Predicate Substitution *}

definition SubstP ::
  " ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_[_]" [200]) where
"\<lbrakk>ss \<in> VAR_SUBST; p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 SubstP p ss = (ss ` (\<alpha> p), (SubstB ss) ` (\<beta> p))"

subsection {* Theorems *}

text {* General Functions *}

theorem bij_comp_inject :
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

theorem VAR_SUBST_inv [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> (inv ss) \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (safe)
apply (drule_tac x = "inv ss v" in spec)
apply (erule subst)
apply (simp add: surj_f_inv_f bij_def)
done

theorem VAR_SUBST_inv_inv [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> inv (inv ss) = ss"
apply (simp add: VAR_SUBST_def)
apply (simp add: inv_inv_eq)
done

theorem VAR_SUBST_ss_inv [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> ss (inv ss x) = x"
apply (simp add: VAR_SUBST_def)
apply (simp add: surj_f_inv_f bij_def)
done

theorem VAR_SUBST_inv_ss [simp] :
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

theorem VAR_SUBST_in_image_simp [simp] :
"\<lbrakk>ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow> (ss x \<in> ss ` a) = (x \<in> a)"
apply (simp add: VAR_SUBST_def)
apply (auto simp: bij_def inj_eq)
done

theorem VAR_SUBST_compose [simp]:
"\<lbrakk> ss1 \<in> VAR_SUBST ; ss2 \<in> VAR_SUBST \<rbrakk> \<Longrightarrow> (ss1 \<circ> ss2) \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (auto simp: bij_def)
apply(simp add:inj_comp)
apply(metis UNIV_I image_compose)
done

theorem VAR_SUBST_id [simp]:
"id \<in> VAR_SUBST"
  by (simp add:VAR_SUBST_def)

theorem VAR_SUBSTS_disj_comm [simp]:
"\<lbrakk> ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST; mappings ss1 \<inter> mappings ss2 = {} \<rbrakk> \<Longrightarrow>
 ss1 \<circ> ss2 = ss2 \<circ> ss1"
  by (auto intro:disj_mapping_comm simp add:VAR_SUBST_def bij_def)

theorem VAR_SUBST_WF_BINDING [simp] :
"\<lbrakk>b \<in> WF_BINDING; ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 b \<circ> ss \<in> WF_BINDING"
apply (simp add: VAR_SUBST_def WF_BINDING_def)
apply (safe)
apply (drule_tac x = "ss v" in spec)
apply (drule_tac x = "v" in spec)
apply (auto)
done

text {* Binding Substitution *}

theorem SubstB_closure [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b \<in> WF_BINDING"
apply (simp add: SubstB_def)
done

theorem SubstsB_inject [simp]:
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (SubstB ss b1 = SubstB ss b2) = (b1 = b2)"
apply (simp add: SubstB_def)
apply (simp add: VAR_SUBST_def)
apply (simp add: bij_comp_inject)
done

theorem SubstB_inv_cancel1 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB (inv ss) (SubstB ss b) = b"
apply (subgoal_tac "SubstB ss b \<in> WF_BINDING")
apply (simp add: SubstB_def)
apply (rule ext)
apply (simp_all)
done

theorem SubstB_inv_cancel2 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (SubstB (inv ss) b) = b"
apply (subgoal_tac "SubstB (inv ss) b \<in> WF_BINDING")
apply (simp add: SubstB_def)
apply (rule ext)
apply (simp_all)
done

theorem SubstB_compose:
"\<lbrakk>ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss1 (SubstB ss2 b) = SubstB (ss1\<circ>ss2) b"
apply(subgoal_tac "SubstB ss2 b \<in> WF_BINDING")
apply(simp add: SubstB_def)
apply(auto simp add:VAR_SUBST_def o_inv_distrib)
done

theorem SubstB_id [simp] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB id b = b"
  by (simp add:SubstB_def)

theorem SubstB_disj_comm [simp] :
"\<lbrakk>ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST;
 b \<in> WF_BINDING; mappings ss1 \<inter> mappings ss2 = {} \<rbrakk> \<Longrightarrow>
 SubstB ss1 (SubstB ss2 b) = SubstB ss2 (SubstB ss1 b)"
  by (metis SubstB_compose VAR_SUBSTS_disj_comm)

lemma SubstB_override1:
"\<lbrakk> ss \<in> VAR_SUBST; a \<in> WF_ALPHABET;
   b \<in> WF_BINDING; b' \<in> WF_BINDING \<rbrakk> \<Longrightarrow>
(SubstB ss b) \<oplus> SubstB ss b' on ss ` a = SubstB ss (b \<oplus> b' on a)"
apply (simp add:SubstB_def)
apply (simp add:override_on_def)
apply(rule ext)
apply(auto)
apply (smt VAR_SUBST_ss_inv imageI)
done


lemma SubstB_override2:
"\<lbrakk> ss \<in> VAR_SUBST; a \<in> WF_ALPHABET;
   b \<in> WF_BINDING; b' \<in> WF_BINDING \<rbrakk> \<Longrightarrow>
SubstB (inv ss) (SubstB ss b \<oplus> b' on ss ` a) = b \<oplus> SubstB (inv ss) b' on a"
apply (simp add:SubstB_def)
apply (simp add:override_on_def)
apply(rule ext)
apply(auto)
done

lemma SubstB_override3:
"\<lbrakk> ss \<in> VAR_SUBST; a \<in> WF_ALPHABET;
   b \<in> WF_BINDING; b' \<in> WF_BINDING; mappings ss \<inter> a = {} \<rbrakk> \<Longrightarrow>
SubstB ss (b \<oplus> b' on a) = (SubstB ss b) \<oplus> (SubstB ss b') on a"
apply(simp add:SubstB_def)
apply(simp add:override_on_def)
apply(rule ext)
apply(auto)
apply(simp add:mappings_def Un_def Int_def)
apply(metis VAR_SUBST_ss_inv)
apply(metis VAR_SUBST_in_image_simp VAR_SUBST_ss_inv disj_mapping_image)
done

lemma SubstB_override4:
"\<lbrakk> ss \<in> VAR_SUBST; a \<in> WF_ALPHABET;
   b \<in> WF_BINDING; b' \<in> WF_BINDING; mappings ss \<inter> a = {} \<rbrakk> \<Longrightarrow>
SubstB ss (b \<oplus> b' on a) = SubstB ss (b \<oplus> (SubstB ss b') on a)"
apply(simp add:SubstB_def)
apply(simp add:override_on_def)
apply(rule ext)
apply(auto)
apply(simp add:mappings_def Un_def Int_def)
apply(metis)
done

lemma SubstB_invol:
"\<lbrakk> ss \<in> VAR_SUBST; b \<in> WF_BINDING; ss \<circ> ss = id \<rbrakk> \<Longrightarrow>
 SubstB ss (SubstB ss b) = b"
  by (metis SubstB_compose SubstB_id)

subsubsection {* Predicate Substitution *}

theorem SubstP_alphabet [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 \<alpha> p[ss] = ss ` (\<alpha> p)"
apply (simp add: SubstP_def)
done

(*
theorem SubstP_alpha_disj_comm [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST; 
 mappings ss1 \<inter> mappings ss2 = {} \<rbrakk> \<Longrightarrow>
*)

text {* Could the following be useful in other places too? Examine! *}

theorem SubstP_closure_lemma :
"\<lbrakk>ss \<in> VAR_SUBST;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b1 \<cong> b2 on ss ` a \<longrightarrow> b1 \<cong> SubstB (inv ss) b2 on a"
apply (simp add: beta_equiv_def)
apply (simp add: SubstB_def)
done

theorem SubstP_closure [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss] \<in> WF_ALPHA_PREDICATE"
apply (simp add: SubstP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (safe)
-- {* Subgoal 1 *}
apply (auto simp: WF_ALPHABET_def)
-- {* Subgoal 2 *}
apply (simp add: WF_BINDING_SET_def)
apply (safe)
-- {* Subgoal 2.1 *}
apply (subgoal_tac "xa \<in> WF_BINDING")
apply (simp)
apply (auto) [1]
-- {* Subgoal 2.2 *}
apply (simp (no_asm_simp) add: image_def)
apply (rule_tac x = "SubstB (inv ss) b2" in bexI)
apply (simp)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "SubstB (inv ss) b2" in bspec)
apply (simp)
apply (subgoal_tac "b1 \<cong> SubstB (inv ss) b2 on \<alpha> p")
apply (simp)
apply (subst SubstP_closure_lemma)
apply (auto)
done

theorem EvalP_SubstP [eval] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP p[ss] b = EvalP p (SubstB (inv ss) b)"
apply (simp add: EvalP_def)
apply (simp add: SubstP_def)
apply (simp add: image_def)
apply (safe)
apply (subgoal_tac "x \<in> WF_BINDING")
apply (simp)
apply (simp add: WF_BINDING_predicate)
apply (rule_tac x = "SubstB (inv ss) b" in bexI)
apply (simp)
apply (assumption)
done

theorem EvalP_SubstsP_SubstB [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 EvalP p[ss] (SubstB ss b) = EvalP p b"
apply (simp add: EvalP_def)
apply (simp add: SubstP_def)
apply (simp add: image_def)
apply (auto)
apply (subgoal_tac "x \<in> WF_BINDING")
apply (simp)
apply (simp add: WF_BINDING_predicate)
done

subsubsection {* Algebraic Laws *}

theorem SubstP_inverse :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss][inv ss] = p"
apply (utp_pred_taut_tac)
done

theorem SubstP_compose :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss1][ss2] = p[ss2\<circ>ss1]"
apply (utp_pred_eq_tac)
apply(rule conjI)
apply(force)
apply(simp add:SubstB_compose)
apply(simp add:o_inv_distrib VAR_SUBST_def)
done

theorem SubstP_disj_comm:
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST
; mappings ss1 \<inter> mappings ss2 = {} \<rbrakk> \<Longrightarrow> p[ss1][ss2] = p[ss2][ss1]"
apply (utp_pred_eq_tac)
apply(rule conjI)
apply(metis SubstP_alphabet SubstP_closure SubstP_compose VAR_SUBSTS_disj_comm)
apply(smt SubstB_closure SubstB_def SubstB_disj_comm SubstB_inv_cancel2 SubstsB_inject VAR_SUBST_inv VAR_SUBST_inv_inv)
done

theorem SubstP_id :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow>
 p[id] = p"
  by (utp_pred_eq_tac)

theorem SubstP_AndP_distr :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<and>p p2)[ss] = p1[ss] \<and>p p2[ss]"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem SubstP_OrP_distr :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<or>p p2)[ss] = p1[ss] \<or>p p2[ss]"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem SubstP_NotP_distr :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (\<not>p p)[ss] = \<not>p p[ss]"
apply (utp_pred_eq_tac)
done

theorem ExistsResP_Subst:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
  ss \<in> VAR_SUBST; a \<in> WF_ALPHABET \<rbrakk> \<Longrightarrow>
  p \<ominus>p a = (p[ss] \<ominus>p (ss ` a))[inv ss]"
apply (utp_pred_eq_tac)
apply(rule conjI)
apply (smt VAR_SUBST_image_inv VAR_SUBST_inv VAR_SUBST_inv_inv image_diff_subset image_mono set_eq_subset)
apply(auto)
apply(rule_tac x="SubstB ss b'" in bexI)
apply(auto simp add:SubstB_override1)
apply(rule_tac x="SubstB (inv ss) b'" in bexI)
apply(auto simp add:SubstB_override2)
done

theorem ResP_Subst_disj:
  assumes "p \<in> WF_ALPHA_PREDICATE" "ss \<in> VAR_SUBST" "a \<in> WF_ALPHABET" "mappings ss \<inter> a = {}"
  shows "(p \<ominus>p a)[ss] = p[ss] \<ominus>p a"
apply(insert assms)
apply(utp_pred_eq_tac)
apply(rule conjI)
apply(simp add:VAR_SUBST_def bij_def image_set_diff disj_mapping_image)
apply(auto)
apply(rule_tac x="SubstB (inv ss) b'" in bexI)
apply (smt SubstB_closure SubstB_inv_cancel2 SubstB_override3 SubstB_override4 VAR_SUBST_inv VAR_SUBST_inv_inv WF_BINDING_override)
apply(force)
apply(rule_tac x="SubstB (inv ss) b'" in bexI)
apply (smt SubstB_closure SubstB_inv_cancel2 SubstB_override2 VAR_SUBST_inv assms(2) disj_mapping_image)
apply(force)
done

theorem ExistsResP_Subst_disj:
  assumes "p \<in> WF_ALPHA_PREDICATE" "ss \<in> VAR_SUBST" "a \<in> WF_ALPHABET" "mappings ss \<inter> a = {}"
  shows "(\<exists>-p a . p)[ss] = (\<exists>-p a . p[ss])"
apply(insert assms)
apply(simp add:ExistsResP_def)
apply(simp add:ResP_Subst_disj)
done

(*
theorem SubstP_ExistsResP :
"\<lbrakk> a \<in> WF_ALPHABET
 ; p \<in> WF_ALPHA_PREDICATE
 ; ss \<in> VAR_SUBST \<rbrakk> \<Longrightarrow>
 (\<exists>-p a . p)[ss] = (\<exists>-p a . p[ss \<oplus> id on a])"
apply(subgoal_tac "ss \<oplus> id on a \<in> VAR_SUBST")
apply(utp_pred_eq_tac)
apply(auto)
*)

theorem Closure_SubstP :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 [p[ss]] = ([p] :: ('VALUE, 'TYPE) ALPHA_PREDICATE)"
apply (utp_pred_taut_tac)
apply (auto)
-- {* Can we automate discharging the following residual subgoal? *}
apply (drule_tac x = "SubstB ss x" in bspec)
apply (simp)
apply (simp add: SubstB_def)
apply (subgoal_tac
  "EvalP p (((b \<oplus> (x \<circ> (inv ss)) on ss ` \<alpha> p) \<circ> ss) \<oplus> x on - \<alpha> p)")
apply (subgoal_tac
  "x = ((b \<oplus> (x \<circ> (inv ss)) on ss ` \<alpha> p) \<circ> ss) \<oplus> x on - \<alpha> p")
apply (simp)
apply (rule ext)
apply (simp add: comp_def)
apply (case_tac "ss xa \<in> ss ` \<alpha> p")
apply (simp)
apply (simp)
apply (simp_all add: EvalP_override)
done

subsection {* Proof Experiments *}

text {*
  The following proof illustrate how we use a mixture of algebraic laws and
  the proof strategy for predicates to proof more complex properties. For now
  the strategy alone is not powerful enough to prove the theorem by itself.
*}

theorem SubstP_lemma1 :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 taut [p1 \<Leftrightarrow>p p2] \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]"
apply (subgoal_tac "p1[ss] \<Leftrightarrow>p p2[ss] = (p1 \<Leftrightarrow>p p2)[ss]")
apply (simp)
apply (simp add: Closure_SubstP)
apply (utp_pred_taut_tac)
apply (utp_pred_eq_tac)
apply (auto)
done
end
end
