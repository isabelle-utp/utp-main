(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_laws.thy                                                   *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Predicate and Relation Laws *}

theory utp_alpha_laws
imports 
  "../alpha/utp_alpha_pred"
  "../alpha/utp_alpha_expr"
  "../alpha/utp_alpha_rel"
  "../tactics/utp_alpha_tac"
  "../tactics/utp_alpha_expr_tac"
  utp_pred_laws
  utp_rename_laws
  utp_subst_laws
  utp_rel_laws
begin

theorem SemiA_extract_variable:
  assumes 
    "x \<in> D\<^sub>0" "x\<acute> \<in>\<^sub>f \<alpha> P" "x \<in>\<^sub>f \<alpha> Q"
    "x\<acute>\<acute> \<notin>\<^sub>f \<alpha> P" "x\<acute>\<acute> \<notin>\<^sub>f \<alpha> Q"
  shows "P ;\<^sub>\<alpha> Q = (\<exists>-\<^sub>\<alpha> \<lbrace>x\<acute>\<acute>\<rbrace>. P[$\<^sub>\<alpha>x\<acute>\<acute>/\<^sub>\<alpha>x\<acute>] ;\<^sub>\<alpha> Q[$\<^sub>\<alpha>x\<acute>\<acute>/\<^sub>\<alpha>x])"
  using assms
  apply (utp_alpha_tac)
  apply (auto)[1]
  apply (rule SemiR_extract_variable)
  apply (simp_all add:unrest)
done

lemma OrA_comm: "p \<or>\<^sub>\<alpha> q = q \<or>\<^sub>\<alpha> p"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma OrA_assoc:
  "p \<or>\<^sub>\<alpha> (q \<or>\<^sub>\<alpha> r) = (p \<or>\<^sub>\<alpha> q) \<or>\<^sub>\<alpha> r"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma OrA_idem [simp]:
  "p \<or>\<^sub>\<alpha> p = p"
  by (utp_alpha_tac)

lemma OrA_left_unit [simp]:
  "false\<^bsub>\<alpha>(p)\<^esub> \<or>\<^sub>\<alpha> p = p"
  by (utp_alpha_tac)

lemma OrA_right_unit [simp]:
  "p \<or>\<^sub>\<alpha> false\<^bsub>\<alpha>(p)\<^esub>  = p"
  by (utp_alpha_tac)

lemma OrA_left_unit_sub:
  "A \<subseteq>\<^sub>f \<alpha>(p) \<Longrightarrow> false\<^bsub>A\<^esub> \<or>\<^sub>\<alpha> p = p"
  by (utp_alpha_tac, auto)

lemma OrA_right_unit_sub:
  "A \<subseteq>\<^sub>f \<alpha>(p) \<Longrightarrow> p \<or>\<^sub>\<alpha> false\<^bsub>A\<^esub> = p"
  by (utp_alpha_tac, auto)

lemma AndA_comm: "p \<and>\<^sub>\<alpha> q = q \<and>\<^sub>\<alpha> p"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma AndA_assoc:
  "p \<and>\<^sub>\<alpha> (q \<and>\<^sub>\<alpha> r) = (p \<and>\<^sub>\<alpha> q) \<and>\<^sub>\<alpha> r"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma AndA_idem [simp]:
  "p \<and>\<^sub>\<alpha> p = p"
  by (utp_alpha_tac)
  
lemma AndA_contra [simp]:
  "p \<and>\<^sub>\<alpha> (\<not>\<^sub>\<alpha> p) = false\<^bsub>\<alpha>(p)\<^esub>"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma AndA_left_zero [simp]:
  "false\<^bsub>A\<^esub> \<and>\<^sub>\<alpha> p = false\<^bsub>A \<union>\<^sub>f \<alpha>(p)\<^esub>"
  by (utp_alpha_tac)

lemma AndA_right_zero [simp]:
  "p \<and>\<^sub>\<alpha> false\<^bsub>A\<^esub> = false\<^bsub>\<alpha>(p) \<union>\<^sub>f A\<^esub>"
  by (utp_alpha_tac)

lemma AndA_OrA_distl: 
  "p \<and>\<^sub>\<alpha> (q \<or>\<^sub>\<alpha> r) = (p \<and>\<^sub>\<alpha> q) \<or>\<^sub>\<alpha> (p \<and>\<^sub>\<alpha> r)"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma AndA_OrA_distr: 
  "(p \<or>\<^sub>\<alpha> q) \<and>\<^sub>\<alpha> r = (p \<and>\<^sub>\<alpha> r) \<or>\<^sub>\<alpha> (q \<and>\<^sub>\<alpha> r)"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma OrA_AndA_distl:
  "p \<or>\<^sub>\<alpha> (q \<and>\<^sub>\<alpha> r) = (p \<or>\<^sub>\<alpha> q) \<and>\<^sub>\<alpha> (p \<or>\<^sub>\<alpha> r)"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma OrA_AndA_distr:
  "(p \<and>\<^sub>\<alpha> q) \<or>\<^sub>\<alpha> r = (p \<or>\<^sub>\<alpha> r) \<and>\<^sub>\<alpha> (q \<or>\<^sub>\<alpha> r)"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma SemiA_AndA_left_precond:
  "\<lbrakk>c \<in> COND; out\<alpha>(c) \<subseteq>\<^sub>f out\<alpha>(q) \<rbrakk> \<Longrightarrow> (c \<and>\<^sub>\<alpha> p) ;\<^sub>\<alpha> q = c \<and>\<^sub>\<alpha> (p ;\<^sub>\<alpha> q)"
  apply (utp_alpha_tac)
  apply (auto)
  apply (metis IntE in_vars_def)
  apply (metis (mono_tags) Un_iff WF_ALPHA_COND_WF_ALPHA_REL WF_ALPHA_REL_unfold in_member out_member set_rev_mp)
  apply (metis (hide_lams, no_types) SemiR_AndP_right_precond SemiR_SkipR_left SemiR_assoc WF_ALPHA_COND_EvalA_WF_CONDITION)
done

thm SemiR_AndP_right_postcond

lemma SemiA_AndA_right_postcond:
  "\<lbrakk> c \<in> POST; in\<alpha>(c) \<subseteq>\<^sub>f in\<alpha>(p) \<rbrakk> \<Longrightarrow> p ;\<^sub>\<alpha> (q \<and>\<^sub>\<alpha> c) = (p ;\<^sub>\<alpha> q) \<and>\<^sub>\<alpha> c"
  apply (utp_alpha_tac)
  apply (auto)
  apply (metis Int_iff out_vars_def)
  apply (smt Int_commute Int_iff REL_ALPHABET_UNDASHED_DASHED REL_ALPHABET_WF_ALPHA_POST Un_iff in_vars_def out_vars_def set_rev_mp)
  apply (metis SemiR_AndP_right_postcond WF_ALPHA_POST_EvalA_WF_POSTCOND)
done

lemma ConvA_rel_closure [closure]: 
  "p \<in> REL \<Longrightarrow> p\<acute> \<in> WF_ALPHA_REL"
  by (metis ConvA_def RenameA_SS_closure)

lemma ConvA_post_closure [closure]: 
  "\<lbrakk> p \<in> COND \<rbrakk> \<Longrightarrow> p\<acute> \<in> WF_ALPHA_POST"
  apply (auto simp add:WF_ALPHA_POST_def WF_ALPHA_COND_def)
  apply (metis ConvA_rel_closure)
  apply (metis EvalA_ConvA EvalA_def SS_UNDASHED_image UNREST_ConvR)
done

lemma ConvA_cond_closure [closure]: 
  "b \<in> POST \<Longrightarrow> b\<acute> \<in> WF_ALPHA_COND"
  apply (auto simp add:WF_ALPHA_POST_def WF_ALPHA_COND_def)
  apply (metis ConvA_rel_closure)
  apply (metis EvalA_ConvA EvalA_def SS_DASHED_image UNREST_ConvR)
done

lemma WF_ALPHA_REL_double_ConvA [simp]: 
  "p \<in> WF_ALPHA_REL \<Longrightarrow> p\<acute>\<acute> = p"
  apply (utp_alpha_tac, auto)
  apply (metis SS_VAR_RENAME_INV VAR_RENAME_INV_app)
  apply (metis SS_VAR_RENAME_INV VAR_RENAME_INV_image_twice image_compose)
done

lemma SkipA_AndA_cond:
  "\<lbrakk> b \<in> COND; \<alpha>(b) \<subseteq>\<^sub>f A; A \<in> REL_ALPHABET; A \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> b \<and>\<^sub>\<alpha> II\<alpha>\<^bsub>A\<^esub> = II\<alpha>\<^bsub>A\<^esub> \<and>\<^sub>\<alpha> b\<acute>"
  apply (utp_alpha_tac, auto)
  apply (metis HOMOGENEOUS_HOM_ALPHA SS_HOMOGENEOUS_image image_eqI set_rev_mp)
  apply (subst SkipRA_AndP_cond)
  apply (metis HOMOGENEOUS_HOM_ALPHA)
  apply (rule UNREST_subset[of "(- D\<^sub>0) \<union> (- \<langle>\<alpha> b\<rangle>\<^sub>f)"])
  apply (simp add:unrest closure)
  apply (auto)
done

lemma SkipA_AndA_post:
  "\<lbrakk> b \<in> POST; \<alpha>(b) \<subseteq>\<^sub>f A; A \<in> REL_ALPHABET; A \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> II\<alpha>\<^bsub>A\<^esub> \<and>\<^sub>\<alpha> b = b\<acute> \<and>\<^sub>\<alpha> II\<alpha>\<^bsub>A\<^esub>"
  apply (subst SkipA_AndA_cond)
  apply (simp_all add:closure urename alphabet)
  apply (auto)
  apply (metis HOMOGENEOUS_HOM_ALPHA Int_iff hom_alphabet_undash in_mono in_vars_def)
  apply (metis (hide_lams, no_types) HOMOGENEOUS_HOM_ALPHA HOMOGENEOUS_out_unprimed in_mono out_vars_union subset_Un_eq)
done

lemma fsubseteq_union1 [alphabet]: "A \<subseteq>\<^sub>f B \<Longrightarrow> A \<union>\<^sub>f B = B"
  by auto

lemma fsubseteq_union2 [alphabet]: "A \<subseteq>\<^sub>f B \<Longrightarrow> B \<union>\<^sub>f A = B"
  by auto

lemma SemiA_FalseA_left: "\<lbrakk> A \<in> REL_ALPHABET; \<alpha>(P) = A \<rbrakk> \<Longrightarrow> false\<^bsub>A\<^esub> ;\<^sub>\<alpha> P = false\<^bsub>A\<^esub>"
  by (utp_alpha_tac)

lemma SemiA_FalseA_right: "\<lbrakk> A \<in> REL_ALPHABET; \<alpha>(P) = A \<rbrakk> \<Longrightarrow> P ;\<^sub>\<alpha> false\<^bsub>A\<^esub>  = false\<^bsub>A\<^esub>"
  by (utp_alpha_tac)

lemma HOM_ALPHABET_SS [urename]:
  "A \<in> HOM_ALPHABET \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s `\<^sub>f A = A"
  apply (auto)
  apply (metis HOMOGENEOUS_HOM_ALPHA SS_HOMOGENEOUS_image imageI)
  apply (metis HOMOGENEOUS_HOM_ALPHA SS_HOMOGENEOUS_image)
done

lemma ConvA_TrueA [urename]: "A \<in> HOM_ALPHABET \<Longrightarrow> true\<^bsub>A\<^esub>\<acute> = true\<^bsub>A\<^esub>"
  by (utp_alpha_tac, simp add:urename)

lemma ConvA_FalseA [urename]: "A \<in> HOM_ALPHABET \<Longrightarrow> false\<^bsub>A\<^esub>\<acute> = false\<^bsub>A\<^esub>"
  by (utp_alpha_tac, simp add:urename)

lemma ConvA_SkipA [urename]: 
  "\<lbrakk> A \<in> REL_ALPHABET; A \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> II\<alpha>\<^bsub>A\<^esub>\<acute> = II\<alpha>\<^bsub>A\<^esub>"
  apply (utp_alpha_tac, simp add:urename)
  apply (utp_rel_auto_tac)
done

lemma ConvA_NotA [urename]: "(\<not>\<^sub>\<alpha> p)\<acute> = \<not>\<^sub>\<alpha> p\<acute>"
  by (utp_alpha_tac, simp add:urename)

lemma ConvA_AndA [urename]: "(p \<and>\<^sub>\<alpha> q)\<acute> = p\<acute> \<and>\<^sub>\<alpha> q\<acute>"
  by (utp_alpha_tac, simp add:urename)

lemma ConvA_OrA [urename]: "(p \<or>\<^sub>\<alpha> q)\<acute> = p\<acute> \<or>\<^sub>\<alpha> q\<acute>"
  by (utp_alpha_tac, simp add:urename)


lemma WF_ALPHA_PRED_cases:
  "\<alpha>(b) \<subseteq>\<^sub>f \<alpha>(P) \<Longrightarrow> P = ((b \<and>\<^sub>\<alpha> P) \<or>\<^sub>\<alpha> \<not>\<^sub>\<alpha> b \<and>\<^sub>\<alpha> P)"
  by (utp_alpha_tac, metis WF_PREDICATE_cases)

thm CondR_def

lemma CondA_alt_def:
  "p \<lhd> b \<rhd>\<^sub>\<alpha> q = ((b \<and>\<^sub>\<alpha> p) \<or>\<^sub>\<alpha> \<not>\<^sub>\<alpha> b \<and>\<^sub>\<alpha> q)"
  by (utp_alpha_tac, utp_pred_auto_tac)

end
