(******************************************************************************)
(* Title: utp/theories/utp_rel.thy                                            *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Relational Predicates *}

theory utp_rel
imports "../generic/utp_gen_pred" "../generic/utp_eval_tactic"
begin

context GEN_PRED
begin

subsection {* Restrictions *}

definition WF_RELATION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_RELATION =
 {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p \<subseteq> UNDASHED \<union> DASHED}"

definition WF_CONDITION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_CONDITION =
 {p . p \<in> WF_RELATION \<and> p = (\<exists>p DASHED . p)}"

subsection {* Substitution *}

text {* The definitions below should probably be in the predicate locale. *}

definition SubstB ::
  "('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING" where
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b = b \<circ> (inv ss)"

definition SubstP ::
  " ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_[_]" [200]) where
"\<lbrakk>ss \<in> VAR_SUBST;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 SubstP p ss = (ss ` (\<alpha> p), (SubstB ss) ` (\<beta> p))"

definition SS1 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS1 v = (
 if dashes (name v) = 1 then (VAR.dash v) else
 if dashes (name v) = 2 then (VAR.undash v) else v)"

definition SS2 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS2 v = (
 if dashes (name v) = 0 then VAR.dash (VAR.dash v) else
 if dashes (name v) = 2 then VAR.undash (VAR.undash v) else v)"

subsection {* Relational Operators *}

definition CondR ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ \<triangleleft> _ \<triangleright> _") where
"p1 \<in> WF_RELATION \<and>
 p2 \<in> WF_RELATION \<and>
 b \<in> WF_CONDITION \<and>
 \<alpha> p1 = \<alpha> p2 \<and>
 \<alpha> b \<subseteq> \<alpha> p1 \<longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) = (b \<and>p p1) \<or>p (\<not>p b \<and>p p2)"

definition SemiR ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" (infixr ";" 140) where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<and>
 COMPOSABLE (\<alpha> r1) (\<alpha> r1) \<longrightarrow>
 r1 ; r2 = (\<exists>-p dash ` (out (\<alpha> r1)) . r1[SS1] \<and>p r2[SS2])"

subsection {* Theorems *}

text {* Variable Substitution *}

theorem VAR_SUBST_inv_closure [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> (inv ss) \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (safe)
apply (auto intro: bij_imp_bij_inv)
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

text {* Binding Substitution *}

theorem SubstB_closure [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b \<in> WF_BINDING"
apply (simp add: SubstB_def WF_BINDING_def)
apply (simp add: VAR_SUBST_def)
apply (safe)
apply (drule_tac x = "inv ss v" in spec)
apply (subgoal_tac "type (inv ss v) = type v")
apply (simp)
apply (drule_tac x = "inv ss v" in spec)
apply (erule subst)
apply (simp add: surj_f_inv_f bij_def)
done

theorem SubstB_cancel1 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB (inv ss) (SubstB ss b) = b"
apply (subgoal_tac "SubstB ss b \<in> WF_BINDING")
apply (simp add: SubstB_def)
apply (rule ext)
apply (simp_all)
done

theorem SubstB_cancel2 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (SubstB (inv ss) b) = b"
apply (subgoal_tac "SubstB (inv ss) b \<in> WF_BINDING")
apply (simp add: SubstB_def)
apply (rule ext)
apply (simp_all)
done

text {* Predicate Substitution *}

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

theorem SubstP_alphabet [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 \<alpha> p[ss] = ss ` (\<alpha> p)"
apply (simp add: SubstP_def)
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

text {* Conditional *}

theorem CondR_closure [simp] :
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) \<in> WF_RELATION"
apply (simp add: CondR_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
done

theorem CondR_alphabet [simp]:
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<triangleleft> b \<triangleright> p2) = \<alpha> p1"
apply (simp add: CondR_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
apply (auto)
done

declare CondR_def [eval]

subsection {* Proof Experiments *}

theorem SubstP_lemma1 [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss][inv ss] = p"
apply (utp_pred_taut_tac)
done

theorem SubstP_lemma2 [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<and>p p2)[ss] = p1[ss] \<and>p p2[ss]"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem SubstP_lemma3 [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 taut [p] \<Leftrightarrow>p [p[ss]]"
apply (utp_pred_taut_tac)
apply (auto)
-- {* This proof is more tricky! *}
oops
end
end