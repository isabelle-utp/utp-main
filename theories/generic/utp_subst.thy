(******************************************************************************)
(* Project: Deep Mechanisation of the UTP                                     *)
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

subsubsection {* Predicate Substitution *}

theorem SubstP_alphabet [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 \<alpha> p[ss] = ss ` (\<alpha> p)"
apply (simp add: SubstP_def)
done

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

theorem SubstP_AndP_distr :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<and>p p2)[ss] = p1[ss] \<and>p p2[ss]"
apply (utp_pred_eq_tac)
apply (auto)
done

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
