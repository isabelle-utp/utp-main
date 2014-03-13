(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_rel_laws.thy                                                     *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Relation Laws *}

theory utp_rel_laws
imports 
  "../core/utp_pred" 
  "../core/utp_rename"
  "../core/utp_expr"
  "../core/utp_rel"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  utp_pred_laws
  utp_rename_laws
  utp_subst_laws
begin

subsection {* Sequential Composition Laws *}

theorem SemiR_OrP_distl :
"p1 ;\<^sub>R (p2 \<or>\<^sub>p p3) = (p1 ;\<^sub>R p2) \<or>\<^sub>p (p1 ;\<^sub>R p3)"
  by (utp_rel_auto_tac)

theorem SemiR_OrP_distr :
"(p1 \<or>\<^sub>p p2) ;\<^sub>R p3 = (p1 ;\<^sub>R p3) \<or>\<^sub>p (p2 ;\<^sub>R p3)"
  by (utp_rel_auto_tac)

theorem SemiR_SkipR_left [simp]:
"II ;\<^sub>R p = p"
  by (utp_rel_auto_tac)

theorem SemiR_SkipR_right [simp]:
"p ;\<^sub>R II = p"
  by (utp_rel_auto_tac)

theorem SemiR_FalseP_left [simp]:
"false ;\<^sub>R p = false"
  by (utp_rel_auto_tac)

theorem SemiR_FalseP_right [simp]:
"p ;\<^sub>R false = false"
  by (utp_rel_auto_tac)

theorem SemiR_assoc :
"p1 ;\<^sub>R (p2 ;\<^sub>R p3) = (p1 ;\<^sub>R p2) ;\<^sub>R p3"
  by (utp_rel_auto_tac)
 
text {* A sequential composition which doesn't mention undashed or dashed variables
        is the same as a conjunction *}

theorem SemiR_equiv_AndP_NON_REL_VAR:
  assumes
    "REL_VAR \<sharp> p"
    "REL_VAR \<sharp> q" 
  shows "p ;\<^sub>R q = p \<and>\<^sub>p q"
  using assms
  apply (utp_rel_auto_tac)
  apply (auto intro: EvalR_UNREST_DASHED_right_intro EvalR_UNREST_DASHED_refl_intro)
  apply (rule EvalR_UNREST_DASHED_right_intro)
  apply (auto)
done

text {* True as a right-identity equates to all dashed variables having values *}

lemma TrueP_right_ExistsP:
  "P ;\<^sub>R true = (\<exists>\<^sub>p D\<^sub>1. P)"
  apply (utp_pred_auto_tac)
  apply (rule_tac x="b1" in exI, simp)
  apply (rule_tac x="b \<oplus>\<^sub>b b' on D\<^sub>1" in exI)
  apply (rule_tac x="SS\<bullet>b' \<oplus>\<^sub>b b on D\<^sub>1 \<union> NON_REL_VAR" in exI)
  apply (auto simp add:COMPOSABLE_BINDINGS_def urename)
  apply (subst binding_equiv_overshadow_left, force)
  apply (metis binding_equiv_sym_elim binding_override_equiv1 binding_override_simps(1))
done

lemma TrueP_right_UNREST_DASHED:
  "p ;\<^sub>R true = p \<longleftrightarrow> D\<^sub>1 \<sharp> p"
  by (metis TrueP_right_ExistsP UNREST_as_ExistsP)

text {* A precondition has true as left identity *}

theorem SemiR_TrueP_precond : 
  assumes "p \<in> WF_CONDITION"
  shows "p ;\<^sub>R true = p"
  by (metis (lifting) ExistsP_ident TrueP_right_ExistsP WF_CONDITION_def assms mem_Collect_eq)

text {* True as a left-identity equates to all undashed variables having values *}

lemma TrueP_left_ExistsP:
  "true ;\<^sub>R P = (\<exists>\<^sub>p D\<^sub>0. P)"
  apply (utp_rel_tac)
  apply (subst EvalR_as_EvalP')
  apply (subst EvalR_as_EvalP')
  apply (simp add:EvalP_ExistsP relcomp_unfold)
  apply (auto)
  apply (rule_tac x="ya" in exI)
  apply (smt UNDASHED_DASHED_inter(16) Un_commute binding_equiv_override binding_override_assoc binding_override_minus binding_override_simps(1) minus_UNDASHED_NON_REL_VAR)
  apply (rule_tac x="xa \<oplus>\<^sub>b b' on D\<^sub>0" in exI)
  apply (auto simp add:closure)
  apply (metis UNDASHED_DASHED_inter(1) binding_override_commute)
  apply (metis binding_equiv_UNDASHED_overshadow binding_equiv_sym_elim)
done

lemma TrueP_left_UNREST_UNDASHED:
  "true ;\<^sub>R p = p \<longleftrightarrow> D\<^sub>0 \<sharp> p"
  by (metis TrueP_left_ExistsP UNREST_as_ExistsP)

text {* A postcondition has true as left identity *}

theorem SemiR_TrueP_postcond :
  assumes "p \<in> WF_POSTCOND"
  shows "true ;\<^sub>R p = p"
  by (metis TrueP_left_UNREST_UNDASHED WF_POSTCOND_def assms mem_Collect_eq)

(*
lemma PrimeP_rel_closure [closure]:
  "p \<in> WF_RELATION \<Longrightarrow> p\<acute> \<in> WF_RELATION"
  apply (simp add:PrimeP_def WF_RELATION_def)
  apply (rule unrest)
  apply (simp)
  apply (metis SS_NON_REL_VAR_image order_refl)
done
*)

(*
declare binding_equiv_comm [intro]
*)

theorem SemiR_AndP_right_DASHED: 
  assumes 
    "DASHED \<sharp> c"
  shows "p ;\<^sub>R (c \<and>\<^sub>p q) = (p \<and>\<^sub>p c\<acute>) ;\<^sub>R q"
  using assms by (utp_rel_auto_tac, blast)

theorem SemiR_AndP_right_precond: 
  assumes 
    "c \<in> WF_CONDITION"
  shows "p ;\<^sub>R (c \<and>\<^sub>p q) = (p \<and>\<^sub>p c\<acute>) ;\<^sub>R q"
  by (metis (full_types) Diff_mono SemiR_AndP_right_DASHED UNDASHED_DASHED_minus(2) UNREST_WF_CONDITION UNREST_subset VAR_subset assms order_refl)

theorem SemiR_AndP_right_UNDASHED: 
  assumes
    "UNDASHED \<sharp> c"
  shows "p ;\<^sub>R (q \<and>\<^sub>p c) = (p ;\<^sub>R q) \<and>\<^sub>p c"
  using assms
  by (utp_rel_auto_tac, blast, blast)

theorem SemiR_AndP_right_postcond: 
  assumes
    "c \<in> WF_POSTCOND"
  shows "p ;\<^sub>R (q \<and>\<^sub>p c) = (p ;\<^sub>R q) \<and>\<^sub>p c"
  using assms
  by (auto intro: SemiR_AndP_right_UNDASHED simp add:WF_POSTCOND_def)

theorem SemiR_AndP_left_UNDASHED: 
  assumes
    "UNDASHED \<sharp> c"
  shows "(p \<and>\<^sub>p c) ;\<^sub>R q = p ;\<^sub>R (c\<acute> \<and>\<^sub>p q)"
  using assms
  by (utp_rel_auto_tac, blast)

theorem SemiR_AndP_left_postcond: 
  assumes
    "c \<in> WF_POSTCOND"
  shows "(p \<and>\<^sub>p c) ;\<^sub>R q = p ;\<^sub>R (c\<acute> \<and>\<^sub>p q)"
  using assms
  by (auto intro: SemiR_AndP_left_UNDASHED simp add:WF_POSTCOND_def)

theorem SemiR_AndP_left_DASHED: 
  assumes
    "DASHED \<sharp> c"
  shows "(c \<and>\<^sub>p p) ;\<^sub>R q = c \<and>\<^sub>p (p ;\<^sub>R q)"
  using assms
  by (utp_rel_auto_tac, blast)

theorem SemiR_AndP_left_precond: 
  assumes
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION"  
    "c \<in> WF_CONDITION"
  shows "(c \<and>\<^sub>p p) ;\<^sub>R q = c \<and>\<^sub>p (p ;\<^sub>R q)"
  using assms
  by (auto intro: SemiR_AndP_left_DASHED simp add:WF_CONDITION_def)

theorem SemiR_TrueP_right_precond:
  assumes "P \<in> WF_CONDITION"
  shows "true ;\<^sub>R P = P\<acute> ;\<^sub>R true"
proof -
  have "true ;\<^sub>R P = true ;\<^sub>R (P \<and>\<^sub>p true)"
    by simp

  also from assms have "... = P\<acute> ;\<^sub>R true"
    by (simp only: SemiR_AndP_right_precond closure, simp)

  ultimately show ?thesis by simp
qed

theorem SemiR_precond_left_zero : 
  assumes 
   "p \<in> WF_CONDITION" 
   "p \<noteq> false"
  shows "true ;\<^sub>R p = true"
proof -
  have "true ;\<^sub>R p = true ;\<^sub>R (p ;\<^sub>R true)"
    by (metis SemiR_TrueP_precond assms)

  also from assms have "... = true"
    apply (utp_xrel_tac)
    apply (auto simp add:relcomp_unfold)
    apply (rule_tac x="fst x" in exI)
    apply (rule_tac x="snd x" in exI)
    apply (simp)
  done

  finally show ?thesis .
qed

theorem SemiR_postcond_right_zero : 
  assumes 
    "p \<in> WF_POSTCOND" 
    "p \<noteq> false"
  shows "p ;\<^sub>R true = true"
proof -
  have "p ;\<^sub>R true = (true ;\<^sub>R p) ;\<^sub>R true"
    by (metis SemiR_TrueP_postcond assms(1))

  also from assms have "... = true"
    apply (utp_xrel_tac)
    apply (auto simp add:relcomp_unfold)
    apply (rule_tac x="snd x" in exI)
    apply (rule_tac x="fst x" in exI)
    apply (simp)
  done

  finally show ?thesis .
qed

theorem SemiR_condition_comp [simp]:
  assumes 
    "p1 \<in> WF_CONDITION"
  shows "\<not>\<^sub>p (\<not>\<^sub>p p1 ;\<^sub>R true) = p1"
  using assms
  by (metis NotP_NotP NotP_cond_closure SemiR_TrueP_precond)

theorem SemiR_TrueP_TrueP [simp]: 
  "true ;\<^sub>R true = true"
  using assms
  by (metis SemiR_TrueP_precond TrueP_cond_closure)

theorem SemiR_cond_idem [simp]:
  assumes "P \<in> WF_CONDITION" 
  shows "P ;\<^sub>R P = P"
  using assms
  by (metis SemiR_FalseP_left SemiR_TrueP_precond SemiR_assoc SemiR_precond_left_zero)

theorem SemiR_postcond_idem [simp]:
  assumes "P \<in> WF_POSTCOND"
  shows "P ;\<^sub>R P = P"
  using assms
  by (metis SemiR_FalseP_right SemiR_TrueP_postcond SemiR_assoc SemiR_postcond_right_zero)

theorem TrueP_left_annihilator_unique:
  assumes 
    "P \<in> WF_RELATION"
    "P ;\<^sub>R true = false"
  shows "P = false"
  using assms
  by (utp_xrel_auto_tac, metis (lifting) prod_caseI2)

theorem TrueP_right_annihilator_unique:
  assumes "P \<in> WF_RELATION"
  shows "true ;\<^sub>R P = false \<Longrightarrow> P = false"
  using assms
  by (utp_xrel_auto_tac, metis (lifting) prod_caseI2)

text {* A precondition followed by a postcondition is a conjunction *}

theorem SemiR_COND_POSTCOND:
  assumes 
    "p \<in> WF_CONDITION" "q \<in> WF_POSTCOND"
  shows "p ;\<^sub>R q = p \<and>\<^sub>p q"
proof -
  from assms have "p ;\<^sub>R true = p" "true ;\<^sub>R q = q"
    by (auto dest:SemiR_TrueP_precond SemiR_TrueP_postcond)
  with assms show ?thesis
    by (utp_xrel_auto_tac)
qed

lemma WF_RELATION_CONDITION_true: 
  assumes "P \<in> WF_RELATION" "(P ;\<^sub>R true) = P"
  shows "P \<in> WF_CONDITION"
proof -
  have "D\<^sub>1 \<sharp> (P ;\<^sub>R true)"
    by (simp add:unrest closure assms(1))

  thus ?thesis
    by (simp add:WF_CONDITION_def assms)
qed

lemma WF_RELATION_POSTCOND_true: 
  assumes "P \<in> WF_RELATION" "(true ;\<^sub>R P) = P"
  shows "P \<in> WF_POSTCOND"
proof -
  have "D\<^sub>0 \<sharp> (true ;\<^sub>R P)"
    by (simp add:unrest closure assms(1))

  thus ?thesis
    by (simp add:WF_POSTCOND_def assms)
qed

lemma SemiR_first_POSTCOND [closure]:
  "\<lbrakk> p \<in> WF_POSTCOND; Q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> p ;\<^sub>R Q \<in> WF_POSTCOND"
  by (metis (full_types) SemiR_TrueP_postcond SemiR_assoc SemiR_closure WF_POSTCOND_WF_RELATION WF_RELATION_POSTCOND_true)

lemma SemiR_second_CONDITION [closure]:
  "\<lbrakk> P \<in> WF_RELATION; q \<in> WF_CONDITION \<rbrakk> \<Longrightarrow> P ;\<^sub>R q \<in> WF_CONDITION"
  by (metis SemiR_TrueP_precond SemiR_assoc SemiR_closure WF_CONDITION_WF_RELATION WF_RELATION_CONDITION_true)

text {* This somewhat odd looking property derives from Relation Algebra. It is used,
        for instance, in the theory of designs. *}

theorem SemiR_TrueP_compl [simp]:
  assumes "P \<in> WF_RELATION"
  shows "\<not>\<^sub>p (P ;\<^sub>R true) ;\<^sub>R true = \<not>\<^sub>p (P ;\<^sub>R true)"
  using assms
  by (utp_xrel_auto_tac)

text {* A single variable can be extracted from a sequential composition and captured
        in an existential *}

theorem SemiR_extract_variable:
  assumes 
    "x \<in> D\<^sub>0" "y \<in> NON_REL_VAR" 
    "vtype x = vtype y" "aux x = aux y"
    "{y} \<sharp> P" "{y} \<sharp> Q"
  shows "P ;\<^sub>R Q = (\<exists>\<^sub>p {y} . P[$\<^sub>ey/\<^sub>px\<acute>] ;\<^sub>R Q[$\<^sub>ey/\<^sub>px])"
  using assms(1-3) assms(5-6)
  apply (utp_pred_auto_tac)
  (* Subgoal 1 *)
  apply (rule_tac x="b1(y :=\<^sub>b \<langle>b1\<rangle>\<^sub>b x\<acute>)" in exI)
  apply (simp)
  apply (rule_tac x="b1(y :=\<^sub>b \<langle>b1\<rangle>\<^sub>b x\<acute>)" in exI)
  apply (rule_tac x="b2(y :=\<^sub>b \<langle>b2\<rangle>\<^sub>b x)" in exI)
  apply (auto)
  apply (simp_all add:assms(4))
  apply (metis (mono_tags) EvalP_UNREST_assign_1 binding_upd_apply binding_upd_simps(2))
  apply (metis (mono_tags) EvalP_UNREST_assign_1 binding_upd_apply binding_upd_simps(2))
  apply (auto simp add:COMPOSABLE_BINDINGS_def)[1]
  apply (metis binding_equiv_minus binding_equiv_update_drop assms)
  (* Subgoal 2 *)
  apply (rule_tac x="b1(x\<acute> :=\<^sub>b \<langle>b1\<rangle>\<^sub>b y, y :=\<^sub>b \<langle>b\<rangle>\<^sub>b y)" in exI)
  apply (rule_tac x="b2(x :=\<^sub>b \<langle>b2\<rangle>\<^sub>b y, y :=\<^sub>b \<langle>b\<rangle>\<^sub>b y)" in exI)
  apply (auto)
  apply (subst binding_upd_twist, force)
  apply (simp)
  apply (metis DASHED_not_NON_REL_VAR UNDASHED_not_DASHED binding_upd_override3 binding_upd_override_extract1 binding_upd_triv binding_upd_upd)
  apply (metis EvalP_UNREST_assign_1)
  apply (metis EvalP_UNREST_assign_1)
  apply (auto simp add:COMPOSABLE_BINDINGS_def assms(4))
  apply (simp add:binding_equiv_def)
  apply (metis (hide_lams, no_types) DASHED_not_NON_REL_VAR NON_REL_VAR_dash_NON_REL_VAR UNDASHED_dash_DASHED binding_equiv_update_subsume binding_equiv_update_subsume' binding_override_left_eq binding_override_singleton)
done

theorem SemiR_extract_variable_id:
  assumes 
    "x \<in> UNDASHED"
    "{x\<acute>\<acute>} \<sharp> P" "{x\<acute>\<acute>} \<sharp> Q"
  shows "P ;\<^sub>R Q = (\<exists>\<^sub>p {x\<acute>\<acute>}. P[$\<^sub>ex\<acute>\<acute>/\<^sub>px\<acute>] ;\<^sub>R Q[$\<^sub>ex\<acute>\<acute>/\<^sub>px])"
  using assms
  by (rule_tac SemiR_extract_variable, simp_all)

text {* If the right hand side of ; restricts less input variables than the less
        does for corresponding outputs, those outputs can be existentially quantified. *}

theorem SemiR_ExistsP_insert_left:
  assumes "undash ` vs \<sharp> Q" "vs \<subseteq> D\<^sub>1"
  shows "P ;\<^sub>R Q = (\<exists>\<^sub>p vs. P) ;\<^sub>R Q"
  using assms
  apply (utp_pred_auto_tac)
  apply (rule_tac x="b1" in exI)
  apply (rule_tac x="b2" in exI)
  apply (auto)
  apply (rule_tac x="b1" in exI, simp)
  apply (rule_tac x="b1 \<oplus>\<^sub>b b' on vs" in exI)
  apply (rule_tac x="b2 \<oplus>\<^sub>b (SS\<bullet>b') on undash ` vs" in exI)
  apply (simp add:eval unrest)
  apply (subst binding_override_left_subset)
  apply (force)
  apply (subst binding_override_right_subset)
  apply (force simp add:var_defs)
  apply (auto simp add:COMPOSABLE_BINDINGS_def)[1]
  apply (case_tac "v\<acute> \<in> vs")
  apply (simp add:urename)
  apply (simp add:urename)
  apply (metis (full_types) dash_undash_image imageI override_on_def)
  apply (subst binding_equiv_overshadow_left)
  apply (auto simp add:var_defs)[1]
  apply (subst binding_equiv_overshadow_right)
  apply (auto simp add:var_defs)[1]
  apply (assumption)
done

theorem SemiR_ExistsP_insert_right:
  assumes "dash ` vs \<sharp> P" "vs \<subseteq> D\<^sub>0" 
  shows "P ;\<^sub>R Q = P ;\<^sub>R (\<exists>\<^sub>p vs. Q)"
  using assms
  apply (utp_pred_auto_tac)
  apply (rule_tac x="b1" in exI)
  apply (rule_tac x="b2" in exI)
  apply (auto)
  apply (rule_tac x="b2" in exI, simp)
  apply (rule_tac x="b1 \<oplus>\<^sub>b (SS\<bullet>b') on dash ` vs" in exI)
  apply (rule_tac x="b2 \<oplus>\<^sub>b b' on vs" in exI)
  apply (simp add:eval unrest)
  apply (subst binding_override_left_subset)
  apply (force)
  apply (auto simp add:closure)[1]
  apply (subst binding_override_right_subset)
  apply (force simp add:var_defs)
  apply (simp)
  apply (auto simp add:COMPOSABLE_BINDINGS_def)[1]
  apply (case_tac "v \<in> vs")
  apply (simp add:urename)
  apply (simp add:urename)
  apply (metis dash_elim image_iff override_on_def)
  apply (subst binding_equiv_overshadow_left)
  apply (auto simp add:var_defs)[1]
  apply (subst binding_equiv_overshadow_right)
  apply (auto simp add:var_defs)[1]
  apply (assumption)
done

subsubsection {* Existential Lifting *}

text {* Lifting of exists around sequential composition requires that p1 and p2 are 
        relations and that p1 does use any of the inputs hidden by vs as inputs *}

theorem ExistsP_SemiR_expand1:
  assumes unrests: "DASHED_TWICE \<sharp> p1" "DASHED_TWICE \<sharp> p2"
  and     noconn:"(dash ` in vs) \<sharp> p1"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  shows "p1 ;\<^sub>R (\<exists>\<^sub>p vs. p2) = (\<exists>\<^sub>p out vs. (p1 ;\<^sub>R p2))"
proof -

  from unrests have "DASHED_TWICE \<sharp> (\<exists>\<^sub>p vs . p2)"
    by (blast intro:unrest)

  with unrests
  have "p1 ;\<^sub>R (\<exists>\<^sub>p vs. p2) = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>(\<exists>\<^sub>p vs . p2)))"
    by (simp add:SemiR_algebraic)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (\<exists>\<^sub>p (SS2 `\<^sub>s vs) . (SS2\<bullet>p2)))"
    by (simp add: RenameP_ExistsP_distr1)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . \<exists>\<^sub>p (SS2 `\<^sub>s vs) . ((SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2)))"
  proof -
    from unrests have "(SS2 `\<^sub>s vs) \<sharp> (SS1\<bullet>p1)"
    proof -

      have "dash ` (in vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:var_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:var_defs)

      moreover from assms have "(dash ` dash ` in vs) \<sharp> (SS1\<bullet>p1)"
        by (smt SS1_UNDASHED_DASHED_image UNREST_RenameP_alt Un_empty_left calculation(1) in_dash in_in le_iff_sup out_dash rename_image_def sup.idem)

      moreover from assms have "(out vs) \<sharp> (SS1\<bullet>p1)"
        apply (rule_tac ?vs1.0="dash ` out vs" in UNREST_RenameP_alt)
        apply (force intro:  UNREST_subset simp add:var_defs)
        apply (auto simp add:image_def SS1_simps closure out_vars_def)
      done

      ultimately show ?thesis using assms
        by (metis (lifting) SS2_UNDASHED_DASHED_image UNREST_union)
    qed

    thus ?thesis
      by (metis (lifting) ExistsP_AndP_expand2)
  qed

  also from assms have "... = (\<exists>\<^sub>p out vs. \<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2))"
  proof -
    have "DASHED_TWICE \<union> dash ` dash ` (in vs) = DASHED_TWICE"
      by (force simp add:var_defs)

    thus ?thesis using assms
      apply (simp add:SS2_simps)
      apply (smt ExistsP_union SS2_UNDASHED_DASHED_image rename_image_def sup_commute)
    done
  qed

  also from assms have "... = (\<exists>\<^sub>p out vs. (p1 ;\<^sub>R p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

theorem ExistsP_SemiR_expand2:
  assumes unrests: "DASHED_TWICE \<sharp> p1" "DASHED_TWICE \<sharp> p2"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  and     noconn:"(undash ` out vs) \<sharp> p2"
  shows "(\<exists>\<^sub>p vs. p1) ;\<^sub>R p2 = (\<exists>\<^sub>p in vs. (p1 ;\<^sub>R p2))"
proof -

  from unrests have "DASHED_TWICE \<sharp> (\<exists>\<^sub>p vs . p1)"
    by (blast intro:unrest)

  with unrests
  have "(\<exists>\<^sub>p vs. p1) ;\<^sub>R p2 = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>(\<exists>\<^sub>p vs . p1)) \<and>\<^sub>p (SS2\<bullet>p2))"
    by (simp add:SemiR_algebraic closure)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . (\<exists>\<^sub>p (SS1 `\<^sub>s vs) . (SS1\<bullet>p1)) \<and>\<^sub>p (SS2\<bullet>p2))"
    by (metis (lifting) RenameP_ExistsP_distr1)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . \<exists>\<^sub>p (SS1 `\<^sub>s vs) . ((SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2)))"
  proof -
    from unrests have "(SS1 `\<^sub>s vs) \<sharp> (SS2\<bullet>p2)"
    proof -

      have "undash ` (out vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:var_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:var_defs)

      moreover from assms have "(dash ` out vs) \<sharp> (SS2\<bullet>p2)"
        apply (rule_tac ?vs1.0="undash ` out vs" in UNREST_RenameP_alt)
        apply (auto simp add:var_member closure calculation var_simps SS2_simps)
        apply (metis (no_types) DASHED_undash_UNDASHED SS2_UNDASHED_app dash_undash_DASHED rev_image_eqI set_rev_mp utp_var.out_DASHED)
      done

      moreover from assms have "(in vs) \<sharp> (SS2\<bullet>p2)"
        apply (rule_tac ?vs1.0="dash ` dash ` in vs" in UNREST_RenameP_alt)
        apply (force intro:  UNREST_subset simp add:var_defs)
        apply (auto simp add:closure image_def)
        apply (rule_tac x="dash (dash x)" in exI)
        apply (auto simp add:SS2_simps)
        apply (metis (lifting) DASHED_dash_DASHED_TWICE SS2_DASHED_TWICE_app UNDASHED_dash_DASHED UnCI le_iff_sup undash_dash utp_var.in_UNDASHED)
      done

      ultimately show ?thesis using assms
        by (metis (lifting) SS1_UNDASHED_DASHED_image UNREST_union)
    qed

    thus ?thesis
      by (metis (lifting) ExistsP_AndP_expand1)
  qed

  also from assms have "... = (\<exists>\<^sub>p in vs. \<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2))"
  proof -
    have "dash ` (out vs) \<union> DASHED_TWICE = DASHED_TWICE"
      by (force simp add:var_defs)

    thus ?thesis using assms
      apply (simp add:SS1_simps)
      apply (smt ExistsP_union SS1_UNDASHED_DASHED_image Un_commute rename_image_def)
    done
  qed

  also from assms have "... = (\<exists>\<^sub>p in vs. (p1 ;\<^sub>R p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

theorem ExistsP_SemiR_NON_REL_VAR_expand1:
  assumes "vs \<sharp> p1" "vs \<subseteq> NON_REL_VAR"
  shows "p1 ;\<^sub>R (\<exists>\<^sub>p vs. p2) = (\<exists>\<^sub>p vs. (p1 ;\<^sub>R p2))"
  using assms
  apply (utp_pred_auto_tac)
  apply (rule_tac x="b'" in exI)
  apply (rule_tac x="b1 \<oplus>\<^sub>b b' on vs" in exI)
  apply (rule_tac x="b2 \<oplus>\<^sub>b b' on vs" in exI)
  apply (auto)
  apply (metis (hide_lams, no_types) binding_override_assoc binding_override_simps(1) binding_override_simps(4) sup.commute)
  apply (simp add:eval)
  apply (simp add:COMPOSABLE_BINDINGS_def)
  apply (auto)
  apply (metis DASHED_not_NON_REL_VAR UNDASHED_dash_DASHED UNDASHED_not_NON_REL_VAR override_on_def set_rev_mp)
  apply (metis binding_override_left_eq)
  apply (rule_tac x="b1 \<oplus>\<^sub>b b on vs" in exI)
  apply (rule_tac x="b2 \<oplus>\<^sub>b b on vs" in exI)
  apply (auto simp add:eval)
  apply (metis binding_override_assoc binding_override_simps(1) binding_override_simps(2) binding_override_simps(3) binding_override_simps(4) binding_override_simps(5) sup.commute)
  apply (rule_tac x="b2" in exI, simp)
  apply (auto simp add:COMPOSABLE_BINDINGS_def)
  apply (metis (full_types) DASHED_minus_NON_REL_VAR Diff_iff UNDASHED_dash_DASHED UNDASHED_minus_NON_REL_VAR override_on_apply_notin)
  apply (metis binding_override_left_eq)
done

theorem ExistsP_SemiR_NON_REL_VAR_expand2:
  assumes "vs \<sharp> p2" "vs \<subseteq> NON_REL_VAR"
  shows "(\<exists>\<^sub>p vs. p1) ;\<^sub>R p2 = (\<exists>\<^sub>p vs. (p1 ;\<^sub>R p2))"
  using assms
  apply (utp_pred_auto_tac)
  apply (rule_tac x="b'" in exI)
  apply (rule_tac x="b1 \<oplus>\<^sub>b b' on vs" in exI)
  apply (rule_tac x="b2 \<oplus>\<^sub>b b' on vs" in exI)
  apply (auto)
  apply (metis (hide_lams, no_types) Un_commute binding_override_assoc binding_override_simps(1) binding_override_simps(4))
  apply (simp add:eval)
  apply (simp add:COMPOSABLE_BINDINGS_def)
  apply (auto)
  apply (metis DASHED_not_NON_REL_VAR UNDASHED_dash_DASHED UNDASHED_not_NON_REL_VAR override_on_def set_rev_mp)
  apply (metis binding_override_left_eq)
  apply (rule_tac x="b1 \<oplus>\<^sub>b b on vs" in exI)
  apply (rule_tac x="b2 \<oplus>\<^sub>b b on vs" in exI)
  apply (auto simp add:eval)
  apply (metis Un_commute binding_override_assoc binding_override_simps(1) binding_override_simps(2) binding_override_simps(3) binding_override_simps(4) binding_override_simps(5))
  apply (rule_tac x="b1" in exI, simp)
  apply (auto simp add:COMPOSABLE_BINDINGS_def)
  apply (metis (full_types) DASHED_minus_NON_REL_VAR Diff_iff UNDASHED_dash_DASHED UNDASHED_minus_NON_REL_VAR override_on_apply_notin)
  apply (metis binding_override_left_eq)
done

theorem ExistsP_UNDASHED_expand_SemiR:
  assumes
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION" 
    "vs \<subseteq> UNDASHED"
  shows "(\<exists>\<^sub>p vs. p) ;\<^sub>R q = (\<exists>\<^sub>p vs. (p ;\<^sub>R q))"
  using assms
  apply (simp add: SemiR_algebraic_rel closure urename)
  apply (subgoal_tac "UNREST vs (SS2\<bullet>q)")
  apply (simp add:ExistsP_AndP_expand1)
  apply (smt ExistsP_union Un_commute)
  apply (rule unrest) 
  apply (auto intro:closure simp add:urename)
done

theorem ExistsP_DASHED_expand_SemiR:
  assumes
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION" 
    "vs \<subseteq> DASHED"
  shows "p ;\<^sub>R (\<exists>\<^sub>p vs. q) = (\<exists>\<^sub>p vs. (p ;\<^sub>R q))"
  using assms
  apply (simp add: SemiR_algebraic_rel closure urename)
  apply (subgoal_tac "UNREST vs (SS1\<bullet>p)")
  apply (simp add:ExistsP_AndP_expand2)
  apply (smt ExistsP_union Un_commute)
  apply (rule unrest) 
  apply (auto intro:closure simp add:urename)
done

text {* The following theorems show that an existential may be inserted or
        dropped from within a sequential composition when the opposing
        relation does not restrict the variables in the quantification *}

(* Note that assumption assumption 2 is automatic under a homogeneous alphabet.
   The following proof is performed by application of existential lifting.

   FIXME: The new tactics probably make these proofs much easier and cleaner...
 *)

theorem SemiR_ExistsP_left:
  assumes
    "DASHED_TWICE \<sharp> p" 
    "DASHED_TWICE \<sharp> q"
    "(DASHED - vs1) \<sharp> p" 
    "(UNDASHED - vs2) \<sharp> q"
    "vs1 \<subseteq> DASHED" 
    "vs2 \<subseteq> UNDASHED"
    "dash ` vs2 \<subseteq> vs1"
  shows "(\<exists>\<^sub>p (vs1 - dash ` vs2). p) ;\<^sub>R q = p ;\<^sub>R q"
proof -

  let ?A = "dash ` out vs1 - dash ` dash ` in vs2"

  from assms have UNREST: "DASHED_TWICE \<sharp> (\<exists>\<^sub>p vs1 - dash ` vs2 . p)"
    by (auto intro:unrest)

  hence "(\<exists>\<^sub>p (vs1 - dash ` vs2). p) ;\<^sub>R q = 
        (\<exists>\<^sub>p DASHED_TWICE .
         (\<exists>\<^sub>p ?A . (SS1\<bullet>p)) \<and>\<^sub>p (SS2\<bullet>q))"
  proof -

    from assms have "vs1 \<subseteq> UNDASHED \<union> DASHED"
      by (auto)

    with UNREST show ?thesis using assms
      apply (simp add: SemiR_algebraic closure urename var_simps)
      apply (simp add: SS1_UNDASHED_DASHED_image[simplified] var_simps var_dist closure)
    done
  qed

  also from assms(4) have "... = (\<exists>\<^sub>p DASHED_TWICE . (\<exists>\<^sub>p ?A . (SS1\<bullet>p) \<and>\<^sub>p (SS2\<bullet>q)))"
  proof -
    from assms(4) have "UNREST ?A (SS2\<bullet>q)"
      apply (rule unrest)
      apply (subgoal_tac "UNDASHED - vs2 \<subseteq> UNDASHED \<union> DASHED")
      apply (simp add: SS2_UNDASHED_DASHED_image[simplified] var_simps var_dist closure)
      apply (auto intro: unrest)
      apply (metis (lifting) DASHED_dash_DASHED_TWICE set_rev_mp utp_var.out_DASHED)
    done

    thus ?thesis
      by (metis ExistsP_AndP_expand1)
  qed

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p) \<and>\<^sub>p (SS2\<bullet>q))"
  proof -
    have "?A \<subseteq> DASHED_TWICE"
      by (auto simp add:var_defs)

    thus ?thesis
      by (metis ExistsP_union sup_absorb1)
  qed

  ultimately show ?thesis using assms UNREST
    by (simp add:SemiR_algebraic)
qed

theorem SemiR_ExistsP_right:
  assumes
    "DASHED_TWICE \<sharp> p" 
    "DASHED_TWICE \<sharp> q"
    "(DASHED - vs1) \<sharp> p" 
    "(UNDASHED - vs2) \<sharp> q"
    "vs1 \<subseteq> DASHED" 
    "vs2 \<subseteq> UNDASHED"
    "vs1 \<subseteq> dash ` vs2"
  shows "p ;\<^sub>R (\<exists>\<^sub>p (vs2 - undash ` vs1). q) = p ;\<^sub>R q"
proof -

  let ?A = "dash ` dash ` in vs2 - (dash ` dash ` in (undash ` vs1) \<union> out (undash ` vs1))"

  from assms have UNREST: "DASHED_TWICE \<sharp> (\<exists>\<^sub>p vs2 - undash ` vs1 . q)"
    by (auto intro:unrest)

  hence "p ;\<^sub>R (\<exists>\<^sub>p (vs2 - undash ` vs1). q) = 
        (\<exists>\<^sub>p DASHED_TWICE .
         (SS1\<bullet>p) \<and>\<^sub>p (\<exists>\<^sub>p ?A . (SS2\<bullet>q)))"
  proof -

    from assms have "vs1 \<subseteq> UNDASHED \<union> DASHED"
      by (auto)

    with UNREST show ?thesis using assms
      apply (simp add: SemiR_algebraic closure urename var_simps)
      apply (subgoal_tac "undash ` vs1 \<subseteq> UNDASHED \<union> DASHED")
      apply (subgoal_tac "vs2 \<subseteq> UNDASHED \<union> DASHED")
      apply (simp add: SS2_UNDASHED_DASHED_image[simplified] var_simps var_dist closure)
      apply (auto)
    done
  qed

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . (\<exists>\<^sub>p ?A . (SS1\<bullet>p) \<and>\<^sub>p (SS2\<bullet>q)))"
  proof -
    from assms(3) have "?A \<sharp> (SS1\<bullet>p)"
      apply (rule unrest)
      apply (subgoal_tac "DASHED - vs1 \<subseteq> UNDASHED \<union> DASHED")
      apply (simp add: SS1_UNDASHED_DASHED_image[simplified] var_simps var_dist closure)
      apply (auto intro: unrest)
      apply (metis DASHED_dash_DASHED_TWICE Int_iff UNDASHED_dash_DASHED in_vars_def)
      apply (metis (lifting) assms(5) dash_undash_image image_eqI out_dash)
    done

    thus ?thesis
      by (smt ExistsP_AndP_expand2)
  qed

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p) \<and>\<^sub>p (SS2\<bullet>q))"
  proof -
    have "?A \<subseteq> DASHED_TWICE"
      by (auto simp add:var_defs)

    thus ?thesis
      by (smt ExistsP_union sup_absorb1)
  qed

  ultimately show ?thesis using assms UNREST
    by (simp add:SemiR_algebraic)
qed

theorem SemiR_remove_middle_unrest1:
  assumes 
    "P \<in> WF_RELATION"
    "R \<in> WF_RELATION"
    "vs \<subseteq> UNDASHED"
    "(VAR - vs) \<sharp> q"
    "dash`vs \<sharp> P"
    "vs \<sharp> R"
    "q \<noteq> false"
  shows "P ;\<^sub>R (q \<and>\<^sub>p R) = P ;\<^sub>R R"
proof -

  let ?vs'' = "dash`dash`vs"

  from assms have "q \<in> WF_CONDITION"
    apply (auto simp add:WF_CONDITION_def WF_RELATION_def)
    apply (rule UNREST_subset, auto)+
  done

  with assms 
  have "P ;\<^sub>R (q \<and>\<^sub>p R) = (\<exists>\<^sub>p D\<^sub>2. (SS1\<bullet>P) \<and>\<^sub>p (SS2\<bullet>(q \<and>\<^sub>p R)))"
    by (simp add:SemiR_algebraic_rel closure urename)

  also from assms 
  have "... = (\<exists>\<^sub>p D\<^sub>2. (SS1\<bullet>P) \<and>\<^sub>p ((SS2\<bullet>q) \<and>\<^sub>p (SS2\<bullet>R)))"
    by (simp add:urename)

  also from assms 
  have "... = (\<exists>\<^sub>p D\<^sub>2. \<exists>\<^sub>p ?vs''. (SS1\<bullet>P) \<and>\<^sub>p ((SS2\<bullet>q) \<and>\<^sub>p (SS2\<bullet>R)))"
  proof -
    from assms have "D\<^sub>2 \<union> ?vs'' = D\<^sub>2"
      by (auto)

    thus ?thesis 
      apply (rule_tac trans) defer
      apply (rule ExistsP_union)
      apply (simp)
    done
  qed

  also from assms
  have "... = (\<exists>\<^sub>p D\<^sub>2. (SS1\<bullet>P) \<and>\<^sub>p (\<exists>\<^sub>p ?vs''. ((SS2\<bullet>q) \<and>\<^sub>p (SS2\<bullet>R))))"
    apply (subst ExistsP_AndP_expand2[THEN sym])
    apply (simp_all)
    apply (rule unrest)
    apply (auto)
    apply (metis (mono_tags) SS1_DASHED_app UNDASHED_dash_DASHED imageI in_mono)
  done

  also from assms
  have "... = (\<exists>\<^sub>p D\<^sub>2. (SS1\<bullet>P) \<and>\<^sub>p (((\<exists>\<^sub>p ?vs''.(SS2\<bullet>q)) \<and>\<^sub>p (SS2\<bullet>R))))"
    apply (subst ExistsP_AndP_expand1[THEN sym]) back
    apply (simp_all)
    apply (rule unrest)
    apply (auto)
    apply (metis (hide_lams, no_types) SS2_UNDASHED_app image_iff set_mp)
  done

  also from assms
  have "... = (\<exists>\<^sub>p D\<^sub>2. (SS1\<bullet>P) \<and>\<^sub>p (SS2\<bullet>R))"
    apply (subst ExistsP_rest_vars) back
    apply (simp_all)
    apply (rule unrest)
    apply (auto)
    apply (smt Diff_iff Rep_VAR_RENAME_VAR SS2_UNDASHED_app VAR_member image_iff set_mp)
    apply (metis RenameP_FalseP RenameP_inverse1)
  done

  also from assms
  have "... = P ;\<^sub>R R"
    by (metis SemiR_algebraic_rel)

  finally show ?thesis .
qed

text {* This property allows conversion of an alphabetised identity into an existential *} 

lemma SubstP_rel_closure [closure]:
  "\<lbrakk> p \<in> WF_RELATION; NON_REL_VAR \<sharp> v; x \<in> REL_VAR; v \<rhd>\<^sub>e x \<rbrakk> 
  \<Longrightarrow> p[v/\<^sub>px] \<in> WF_RELATION"
  by (auto intro:unrest simp add:WF_RELATION_def unrest typing)

theorem SemiR_left_one_point:
  assumes "x \<in> D\<^sub>0" "v \<rhd>\<^sub>e x" "D\<^sub>1 \<sharp> v" "{x} \<sharp> v"
  shows "P ;\<^sub>R ($\<^sub>ex ==\<^sub>p v \<and>\<^sub>p Q) = P[v\<acute>/\<^sub>px\<acute>] ;\<^sub>R Q[v/\<^sub>px]"
  using assms
  apply (utp_rel_auto_tac)
  apply (metis binding_upd_simps(2))
  apply (rule_tac x="ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>eya) \<oplus>\<^sub>b y on NON_REL_VAR" in exI)
  apply (auto)
  apply (metis EvalE_UNREST_binding_upd EvalR_NON_REL_VAR_elim binding_override_equiv)
  apply (metis EvalR_NON_REL_VAR_elim binding_override_equiv)
done

lemma xbinding_upd_refl [simp]: 
  "x \<in> UNDASHED \<Longrightarrow> b(x :=\<^sub>x \<langle>\<langle>b\<rangle>\<^sub>x\<rangle>\<^sub>b x) = b"
  by (auto simp add:typing defined)

theorem SemiR_right_one_point:
  assumes 
    "x \<in> D\<^sub>0" "v \<rhd>\<^sub>e x" "D\<^sub>1 \<sharp> v" "{x} \<sharp> v"
  shows "(P \<and>\<^sub>p $\<^sub>ex\<acute> ==\<^sub>p v\<acute>) ;\<^sub>R Q = P[v\<acute>/\<^sub>px\<acute>] ;\<^sub>R Q[v/\<^sub>px]"
  using assms
  apply (utp_rel_auto_tac)
  apply (metis binding_upd_simps(2))
  apply (rule_tac x="ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>eya)" in exI)
  apply (auto)
  apply (metis EvalE_UNREST_binding_upd)
done

theorem SemiR_right_one_point_alt:
  assumes 
    "x \<in> D\<^sub>1" "v \<rhd>\<^sub>e x" "D\<^sub>0 \<sharp> v" "{x} \<sharp> v"
  shows "(P \<and>\<^sub>p $\<^sub>ex ==\<^sub>p v) ;\<^sub>R Q = P[v/\<^sub>px] ;\<^sub>R Q[v\<acute>/\<^sub>px~]"
proof -

  from assms have u1: "DASHED \<sharp> v\<acute>"
    by (simp add:urename unrest)

  from assms have u2: "{x~} \<sharp> v\<acute>"
    by (simp add:urename unrest)

  thus ?thesis
    apply (insert SemiR_right_one_point[of "x~" "v\<acute>" P Q])
    apply (simp add:urename closure assms unrest typing u1 u2)
  done
qed

subsubsection {* Alphabetised Skip laws *}

lemma SkipRA_alt_in_def:
  "HOMOGENEOUS vs \<Longrightarrow> II\<^bsub>vs\<^esub> = (\<exists>\<^sub>p (D\<^sub>0 - in vs). II)"
  apply (utp_pred_auto_tac)
  apply (rule_tac x="SS\<bullet>b" in exI, auto)
  apply (metis DiffI SS_UNDASHED_app comp_apply override_on_def)
  apply (metis override_on_minus set_mp in_UNDASHED)
done

lemma SkipRA_alt_out_def:
  "HOMOGENEOUS vs \<Longrightarrow> II\<^bsub>vs\<^esub> = (\<exists>\<^sub>p (D\<^sub>1 - out vs). II)"
  apply (utp_pred_auto_tac)
  apply (rule_tac x="SS\<bullet>b" in exI, auto)
  apply (case_tac "v\<acute> \<in> out vs")
  apply (simp_all add:urename)
  apply (metis Int_iff hom_alphabet_dash in_vars_def out_vars_def)
  apply (drule_tac x="v" in bspec, simp add:var_defs)
  apply (simp)
  apply (metis HOMOGENEOUS_dash_in imageI override_on_minus)
done

theorem SkipRA_left_as_ExistsP:
  assumes 
    "HOMOGENEOUS vs2" 
    "vs1 \<subseteq> D\<^sub>0"
    "D\<^sub>0 - vs1 \<sharp> p"
  shows "II\<^bsub>vs2\<^esub> ;\<^sub>R p = (\<exists>\<^sub>p vs1 - in vs2. p)"
  using assms
  apply (utp_pred_auto_tac)
  (* Subgoal 1 (==>) *)
  apply (simp add:COMPOSABLE_BINDINGS_def, clarify)
  apply (rule_tac x="b2" in exI, simp)
  apply (subst binding_override_minus)
  apply (simp add:var_dist)
  apply (subst Int_commute)
  apply (subst inter_not_DASHED)
  apply (simp add:var_dist)
  (* Three overridings: NON_REL_VAR - nrel vs1, in (- vs1), and in vs2 *)
  (* Case 1 *)
  apply (subst binding_override_simps(1)[THEN sym])
  apply (subst binding_override_equiv_subset[of _ _ "NON_REL_VAR"]) back 
  apply (drule binding_equiv_comm)
  apply (metis binding_override_left_eq binding_override_simps(2))
  apply (force)
  (* Case 2 *)
  apply (subst Un_commute)
  apply (subst binding_override_simps(1)[THEN sym])
  apply (subst EvalP_UNREST_override)
  apply (rule UNREST_subset)
  apply (simp)
  apply (force simp add:var_defs)
  (* Case 3 *)
  apply (metis (hide_lams, no_types) binding_equiv_def binding_override_equiv set_rev_mp utp_var.in_UNDASHED)
  (* Subgoal 2 (<==) *)
  apply (rule_tac x="b \<oplus>\<^sub>b SS\<bullet>(b \<oplus>\<^sub>b b' on vs1 - in vs2) on D\<^sub>1" in exI)
  apply (rule_tac x="(b \<oplus>\<^sub>b b' on vs1 - in vs2) \<oplus>\<^sub>b b on D\<^sub>1" in exI)
  apply (auto)
  apply (subgoal_tac "v \<in> D\<^sub>0")
  apply (simp add:closure urename)
  apply (metis in_mono utp_var.in_UNDASHED)
  apply (metis (hide_lams, no_types) Int_Diff binding_override_reorder binding_override_simps(2) inf_commute inf_le1 out_of_UNDASHED out_vars_def)
  apply (simp add:COMPOSABLE_BINDINGS_def)
  apply (auto simp add:urename)
  apply (subst binding_equiv_overshadow_left)
  apply (force)
  apply (subst binding_equiv_overshadow_right)
  apply (force)
  apply (subst binding_equiv_overshadow_right)
  apply (auto)
done

theorem SkipRA_right_as_ExistsP:
  assumes 
    "HOMOGENEOUS vs2" 
    "vs1 \<subseteq> D\<^sub>1"
    "D\<^sub>1 - vs1 \<sharp> p"
  shows "p ;\<^sub>R II\<^bsub>vs2\<^esub> = (\<exists>\<^sub>p vs1 - out vs2. p)"
  using assms
  apply (utp_pred_auto_tac)
  (* Subgoal 1 (==>) *)
  apply (simp add:COMPOSABLE_BINDINGS_def, clarify)
  apply (rule_tac x="b1" in exI)
  apply (subst binding_override_minus)
  apply (simp add:var_dist)
  apply (subst binding_override_minus)
  apply (simp add:var_dist)
  apply (subst Int_commute)
  apply (subst out_vars_def[THEN sym])
  apply (simp add:var_dist)
  apply (subst Un_commute)
  apply (subst binding_override_simps(1)[THEN sym])
  apply (subst EvalP_UNREST_override)
  apply (rule UNREST_subset)
  apply (simp)
  apply (force simp add:var_defs)
  apply (subgoal_tac "b1 \<cong> b2 on out vs2")
  apply (metis binding_override_equiv)
  apply (auto simp add:binding_equiv_def)
  apply (subgoal_tac "x \<in> D\<^sub>1")
  apply (drule_tac x="x~" in bspec)
  apply (metis (full_types) DASHED_undash_UNDASHED Int_iff dash_undash_DASHED hom_alphabet_dash in_vars_def out_vars_def)
  apply (drule_tac x="x~" in bspec)
  apply (metis DASHED_undash_UNDASHED in_mono utp_var.out_DASHED)
  apply (simp)
  apply (force simp add:var_defs)
  (* Subgoal 2 (<==) *)
  apply (rule_tac x="(b \<oplus>\<^sub>b b' on vs1 - out vs2)" in exI)
  apply (rule_tac x="SS\<bullet>(b \<oplus>\<^sub>b b' on vs1 - out vs2) \<oplus>\<^sub>b b on D\<^sub>1" in exI)

  apply (auto)
  apply (subst binding_override_left_subset)
  apply (force)
  apply (simp)
  apply (subgoal_tac "v \<in> D\<^sub>0")
  apply (simp add:closure urename)
  apply (metis (full_types) HOMOGENEOUS_dash_in binding_override_on.rep_eq binding_override_simps(9) imageI)
  apply (metis in_mono utp_var.in_UNDASHED)
  apply (simp add:COMPOSABLE_BINDINGS_def)
  apply (auto simp add:urename)
  apply (subst binding_equiv_overshadow_left)
  apply (force)
  apply (subst binding_equiv_overshadow_right)
  apply (force)
  apply (simp add:SS_equiv_NON_REL_VAR)
  apply (subst binding_equiv_overshadow_right)
  apply (auto)
done

theorem SemiR_right_ExistsP:
  assumes 
    "p \<in> WF_RELATION" 
    "x \<in> UNDASHED"
  shows "p ;\<^sub>R II\<^bsub>(REL_VAR - {x,x\<acute>})\<^esub> = (\<exists>\<^sub>p {x\<acute>}. p)"
  using assms
  apply (subgoal_tac "REL_VAR - (REL_VAR - {x, x\<acute>}) = {x,x\<acute>}")
  apply (auto simp add:SkipRA_def closure unrest ExistsP_SemiR_expand1 var_dist SkipR_ExistsP_out)
done

theorem SemiR_SkipRA_left :
  assumes 
    "HOMOGENEOUS vs" 
    "D\<^sub>0 - in vs \<sharp> p"
  shows "II\<^bsub>vs\<^esub> ;\<^sub>R p = p"
  using assms
  apply (subst SkipRA_left_as_ExistsP[of _ "in vs"])
  apply (auto simp add:ExistsP_empty)
done

theorem SemiR_SkipRA_right :
  assumes 
    "HOMOGENEOUS vs" 
    "D\<^sub>1 - out vs \<sharp> p"
  shows "p ;\<^sub>R II\<^bsub>vs\<^esub> = p"
  using assms
  apply (subst SkipRA_right_as_ExistsP[of _ "out vs"])
  apply (auto simp add:ExistsP_empty)
done

theorem SkipRA_empty :
  "II\<^bsub>{}\<^esub> = true"
  apply (simp add:SkipRA_def)
  apply (utp_pred_tac)
  apply (rule_tac x="\<B>" in exI)
  apply (simp add:default_binding.rep_eq)
done

theorem SkipRA_unfold :
  assumes 
    "x \<in> vs" 
    "x\<acute> \<in> vs" 
    "x \<in> UNDASHED" 
    "HOMOGENEOUS vs"
  shows "II\<^bsub>vs\<^esub> = $\<^sub>ex\<acute> ==\<^sub>p $\<^sub>ex \<and>\<^sub>p II\<^bsub>(vs - {x,x\<acute>})\<^esub>"
proof -

  have "(UNDASHED \<union> DASHED - vs) \<inter> (UNDASHED \<union> DASHED - (vs - {x, x\<acute>})) = UNDASHED \<union> DASHED - vs"
    by (force)


  (* The proof below proceeds by showing that any variable v is identified by both sides
     of the goal. The are three cases of v:
     1) v = x
     2) v \<noteq> x and v \<in> vs
     3) v \<noteq> x and v \<notin> vs
  *)

  with assms show ?thesis
    apply (simp add:SkipRA_def)
    apply (utp_pred_tac)
    apply (safe)
    (* Subgoal 1 *)
    apply (force)
    (* Subgoal 2 *)
    apply (rule_tac x="b \<oplus>\<^sub>b b' on UNDASHED \<union> DASHED - vs" in exI)
    apply (simp_all add:closure)
    (* Subgoal 3 *)
    apply (rule_tac x="b'" in exI)
    apply (rule ballI)
    apply (case_tac "v=x")
    (* Subgoal 3.1 (Case 1) *)
    apply (simp_all)
    apply (case_tac "v \<in> vs")
    (* Subgoal 3.2 (Case 2) *)
    apply (simp_all)
    apply (erule_tac v="v" in hom_alphabet_undash)
    apply (simp_all)
    apply (drule_tac x="v" in bspec)
    apply (simp)
    apply (subgoal_tac "dash v \<noteq> dash x")
    apply (subgoal_tac "v \<in> vs - {x, dash x}")
    apply (subgoal_tac "dash v \<in> vs - {x, dash x}")
    apply (simp)
    apply (force)
    apply (force)
    apply (metis undash_dash)
    (* Subgoal 3.3 (Case 3) *)
    apply (subgoal_tac "dash v \<in> UNDASHED \<union> DASHED - vs")
    apply (force)
    apply (simp)
    apply (metis hom_alphabet_dash)
  done
qed

lemma SubstP_SkipR_UNDASHED [usubst]:
  assumes 
    "x \<in> UNDASHED"
    "v \<rhd>\<^sub>e x"
  shows "(II[v/\<^sub>px]) = (x :=\<^sub>R v)"
  apply (simp add: SkipR_as_SkipRA)
  apply (subst SkipRA_unfold[of x])
  apply (simp_all add:assms closure usubst typing defined AssignR_alt_def)
done

theorem SkipRA_compose [simp]:
  assumes 
    "HOMOGENEOUS vs1"
    "HOMOGENEOUS vs2" 
    "vs1 \<subseteq> REL_VAR" 
    "vs2 \<subseteq> REL_VAR"
  shows "II\<^bsub>vs1\<^esub> ;\<^sub>R II\<^bsub>vs2\<^esub> = II\<^bsub>vs1 \<inter> vs2\<^esub>"
  using assms
  apply (subgoal_tac "vs1 \<inter> vs2 \<subseteq> REL_VAR")
  apply (auto simp add:evalrx closure relcomp_unfold var_dist)
  apply (rule_tac x="y \<oplus>\<^sub>x xa on (vs1 - vs2)" in exI)
  apply (auto)
  apply (case_tac "x \<in> vs2")
  apply (auto)
done

theorem SkipR_neq_FalseP [simp]:
  "II \<noteq> false" 
  "false \<noteq> II"
  by (utp_xrel_auto_tac, utp_xrel_auto_tac)

text {* This lemma needs to be proved in the context of the BOOL SORT 
        (or any sort with at least two elements) *}

lemma SkipR_neq_TrueP_BOOL_SORT [simp]:
  "(II :: ('a::BOOL_SORT) WF_PREDICATE) \<noteq> true"
proof -
  let ?x = "MkPlain ''x'' BoolType True"

  let ?b1 = "\<B>(?x :=\<^sub>b MkBool True) \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR"
  and ?b2 = "\<B>(?x :=\<^sub>b MkBool False) \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR"

  have "?b1 \<noteq> ?b2"
    apply (auto elim!:Rep_WF_BINDING_elim simp add:typing defined closure fun_eq_iff)
    apply (drule_tac x="?x" in spec)
    apply (simp add:typing defined closure)
  done

  thus ?thesis
    apply (utp_xrel_auto_tac)
    apply (simp add:set_eq_iff)
    apply (drule_tac x="(MkXRelB ?b1, MkXRelB ?b2)" in spec)
    apply (auto)
  done
qed

lemmas TrueP_neq_SkipR_BOOL_SORT [simp] = SkipR_neq_TrueP_BOOL_SORT[THEN not_sym]

subsection {* Assignment Laws *}

theorem AssignR_SemiR_left:
  assumes
    "x \<in> UNDASHED" 
    "e \<rhd>\<^sub>e x" 
    "DASHED \<sharp> e"
  shows "x :=\<^sub>R e ;\<^sub>R p = p[e/\<^sub>px]"
  using assms
  apply (utp_rel_auto_tac)
  apply (subgoal_tac "xa(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>exa) \<in> WF_REL_BINDING")
  apply (simp add:WF_REL_BINDING_def)
  apply (auto)
  apply (rule_tac x="b(x :=\<^sub>b \<langle>xa\<rangle>\<^sub>b x)" in exI)
  apply (subgoal_tac "b(x :=\<^sub>b \<langle>xa\<rangle>\<^sub>b x) \<oplus>\<^sub>b bc on DASHED = (b \<oplus>\<^sub>b bc on DASHED)(x :=\<^sub>b \<langle>xa\<rangle>\<^sub>b x)")
  apply (drule sym)
  apply (simp_all add:typing)
done

lemma AssignRA_alt_def:
  assumes 
    "x \<in> vs" 
    "x\<acute> \<in> vs" 
    "x \<in> UNDASHED" 
    "REL_VAR - vs \<sharp> v" 
    "v \<rhd>\<^sub>e x"
  shows "x :=\<^bsub>vs\<^esub> v = $\<^sub>ex\<acute> ==\<^sub>p v \<and>\<^sub>p II\<^bsub>(vs - {x,x\<acute>})\<^esub>"
using assms
proof (simp add:SkipRA_def AssignRA_def AssignR_alt_def)
  from assms have "REL_VAR - (vs - {x, x\<acute>}) = (REL_VAR - vs) \<union> {x, x\<acute>}"
    by (auto)

  hence "(\<exists>\<^sub>p REL_VAR - (vs - {x, x\<acute>}) . II) = (\<exists>\<^sub>p REL_VAR - vs. \<exists>\<^sub>p {x, x\<acute>} . II)"
    by (metis (lifting) ExistsP_union)

  moreover from assms have "(REL_VAR - vs) \<sharp> ($\<^sub>ex\<acute> ==\<^sub>p v)"
    by (rule_tac unrest, auto intro:unrest)

  ultimately show "(\<exists>\<^sub>p REL_VAR - vs . $\<^sub>ex\<acute> ==\<^sub>p v \<and>\<^sub>p (\<exists>\<^sub>p {x, x\<acute>} . II)) =
                    $\<^sub>ex\<acute> ==\<^sub>p v \<and>\<^sub>p (\<exists>\<^sub>p insert x (insert x\<acute> (REL_VAR - vs)) . II)"
    by (smt ExistsP_AndP_expand2 ExistsP_union Un_empty_right Un_insert_right union_minus)
qed

lemma EvalR_AssignRA [evalr]:
  assumes 
    "x \<in> vs" "x\<acute> \<in> vs" 
    "x \<in> UNDASHED"
    "vs \<subseteq> UNDASHED \<union> DASHED" 
    "HOMOGENEOUS vs"
    "(VAR - in vs) \<sharp> v" 
    "v \<rhd>\<^sub>e x"
  shows "\<lbrakk>x :=\<^bsub>vs\<^esub> v\<rbrakk>R = { (b1, b2) 
                       . b1 \<cong> b2 on (in vs - {x}) \<and> b1 \<cong> b2 on NON_REL_VAR 
                       \<and> \<langle>b2\<rangle>\<^sub>b x = \<lbrakk>v\<rbrakk>\<^sub>eb1 \<and> b1 \<in> WF_REL_BINDING \<and> b2 \<in> WF_REL_BINDING}"
proof -

  have "(vs - {x,x\<acute>}) \<subseteq> REL_VAR"
    by (metis Diff_subset assms(4) subset_trans)

  moreover from assms(6) have "REL_VAR - vs \<sharp> v"
    by (auto intro: UNREST_EXPR_subset simp add:var_defs)

  moreover from assms(6) have "DASHED \<sharp> v"
    apply (rule UNREST_EXPR_subset)
    apply (auto simp add:var_defs)
  done

  ultimately show ?thesis using assms
    apply (simp add: AssignRA_alt_def EvalR_AndP EvalR_SkipRA'' EvalR_EqualP_alt' evale BindR_def Collect_conj_pair_eq)
    apply (rule Collect_eq_pair_intro)
    apply (simp add:var_dist)
    apply (safe)
 done
qed

lemma EvalP_AssignRA [eval]:
  assumes 
    "x \<in> xs" "x\<acute> \<in> xs" 
    "xs \<subseteq> REL_VAR" 
    "HOMOGENEOUS xs"
    "(VAR - in(xs)) \<sharp> e" 
    "e \<rhd>\<^sub>e x"
  shows "\<lbrakk>x :=\<^bsub>xs\<^esub> e\<rbrakk>b = (\<forall> v \<in> in(xs). if (v = x) then \<langle>b\<rangle>\<^sub>b (v\<acute>) = (vcoerce (\<lbrakk>e\<rbrakk>\<^sub>eb) x)
                                                 else \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>b\<rangle>\<^sub>b v)"
  apply (subgoal_tac "x \<in> D\<^sub>0")
  apply (subst AssignRA_alt_def)
  apply (simp_all add: assms)
  apply (rule UNREST_EXPR_subset)
  apply (rule assms)
  apply (force simp add:var_defs)
  apply (simp add:eval closure assms)
  apply (safe)
  apply (drule_tac x="v" in bspec)
  apply (simp add:var_dist assms)
  apply (force)
  apply (metis assms(1) assms(3) in_member)
  apply (drule_tac x="v" in bspec)
  apply (auto simp add:var_dist closure assms)
  apply (metis ComplD DASHED_dash_DASHED_TWICE NON_REL_VAR_UNDASHED_DASHED UnE assms(1) assms(2) assms(3) set_rev_mp utp_var.DASHED_TWICE_NON_REL_VAR)
done

(*
lemma EvalR_AssignRA_alt [evalr]:
  assumes 
    "x \<in> vs" 
    "x\<acute> \<in> vs" 
    "x \<in> UNDASHED"
    "vs \<subseteq> UNDASHED \<union> DASHED" 
    "HOMOGENEOUS vs"
    "DASHED \<union> NON_REL_VAR \<sharp> v" 
    "(REL_VAR - vs) \<sharp> v" 
    "v \<rhd>\<^sub>e x"
  shows "\<lbrakk>x :=\<^bsub>vs\<^esub> v\<rbrakk>R = { (b1, b2) 
                       . b1 \<cong> b2 on (in vs - {x}) 
                       \<and> b1 \<cong> b2 on NON_REL_VAR 
                       \<and> b1 \<cong> bc on DASHED
                       \<and> b2 \<cong> bc on DASHED
                       \<and> \<langle>b2\<rangle>\<^sub>b x = \<lbrakk>v\<rbrakk>\<^sub>eb1}"
  apply (simp add: EvalR_AssignRA assms)
  apply (auto)
  apply (rule binding_override_left_eq, simp)
  apply (rule binding_override_left_eq, simp add:assms)
  apply (metis EvalE_UNREST_override UNDASHED_not_DASHED UNREST_EXPR_unionE assms(3) assms(6) override_on_def)
  apply (metis binding_override_equiv)
done
*)

theorem AssignRA_SemiR_left:
  assumes 
    "x \<in> UNDASHED" 
    "x \<in> vs" 
    "e \<rhd>\<^sub>e x" 
    "HOMOGENEOUS vs" 
    "vs \<subseteq> UNDASHED \<union> DASHED"
    "(VAR - vs) \<sharp> p" 
    "(VAR - in vs) \<sharp> e"
  shows "(x :=\<^bsub>vs\<^esub> e ;\<^sub>R p) = p[e/\<^sub>px]"
proof -

  from assms have "DASHED_TWICE \<sharp> (x :=\<^sub>R e)" 
    apply (rule_tac UNREST_subset)
    apply (rule unrest)
    apply (auto)
    apply (rule UNREST_EXPR_subset)
    apply (auto)
  done

  moreover from assms have "DASHED_TWICE \<sharp> p" 
    by (rule_tac UNREST_subset, auto intro:unrest)

  moreover from assms have 
    "UNDASHED \<union> DASHED - vs \<subseteq> UNDASHED \<union> DASHED" and
    "(undash ` out (UNDASHED \<union> DASHED - vs)) \<sharp> p"
    "DASHED \<sharp> e"
    apply (auto intro:unrest)
    apply (rule_tac UNREST_subset)
    apply (simp)
    apply (simp add:var_dist)
    apply (force)
    apply (rule UNREST_EXPR_subset)
    apply (simp)
    apply (force)
  done

  moreover from assms have "(in (UNDASHED \<union> DASHED - vs)) \<sharp> (p[e/\<^sub>px])"
    apply (rule_tac UNREST_subset[of "(VAR - vs) \<inter> (VAR - in vs)"])
    apply (rule_tac UNREST_SubstP)
    apply (simp_all add:var_dist)
    apply (force)
  done

  ultimately show ?thesis using assms
    apply (simp add:AssignRA_def)
    apply (rule trans)
    apply (rule ExistsP_SemiR_expand2)
    apply (simp_all)
    apply (simp add: AssignR_SemiR_left ExistsP_ident)
  done
qed

theorem SkipRA_assign :
  assumes 
    "x \<in> vs" 
    "x\<acute> \<in> vs" 
    "x \<in> UNDASHED" 
    "HOMOGENEOUS vs"
  shows "II\<^bsub>vs\<^esub> = x :=\<^bsub>vs\<^esub> $\<^sub>ex"
  apply (subgoal_tac "UNREST_EXPR (UNDASHED \<union> DASHED - vs) (VarE x)")
  apply (subgoal_tac "VarE x \<rhd>\<^sub>e x")
  apply (simp add:assms SkipRA_unfold[of x vs] AssignRA_alt_def[of x vs "VarE x"])
  apply (simp add:typing)
  apply (rule UNREST_EXPR_VarE)
  apply (force simp add:assms)
done

theorem AssignR_commute: 
  assumes 
    "x \<in> UNDASHED" "y \<in> UNDASHED"  
    "DASHED \<sharp> e" "DASHED \<sharp> f"
    "{x} \<sharp> f" "{y} \<sharp> e"
    "e \<rhd>\<^sub>e x" "f \<rhd>\<^sub>e y"
    "x \<noteq> y"
  shows "(x :=\<^sub>R e;\<^sub>R y :=\<^sub>R f) = (y :=\<^sub>R f;\<^sub>R x :=\<^sub>R e)"
  using assms
  apply (utp_rel_tac, simp add:relcomp_unfold)
  apply (utp_expr_tac)
  apply (metis (hide_lams, no_types) EvalE_compat WF_REL_BINDING_binding_upd binding_upd_twist)
done

theorem AssignR_idem :
  assumes 
    "x \<in> UNDASHED" 
    "{x} \<sharp> v" 
    "DASHED \<sharp> v" 
    "v \<rhd>\<^sub>e x"
  shows "(x :=\<^sub>R v ;\<^sub>R x :=\<^sub>R v) = x :=\<^sub>R v"
using assms
  apply (utp_rel_auto_tac)
  apply (simp_all add: EvalE_UNREST_assign[of _ "{x}"])
  apply (auto simp add:WF_REL_BINDING_def)
done

theorem AssignRA_idem :
  assumes 
    "x \<in> vs" 
    "x\<acute> \<in> vs" 
    "x \<in> UNDASHED"
    "vs \<subseteq> UNDASHED \<union> DASHED" 
    "HOMOGENEOUS vs"
    "(VAR - (in vs - {x})) \<sharp> v" 
    "v \<rhd>\<^sub>e x"
  shows "x :=\<^bsub>vs\<^esub> v ;\<^sub>R x :=\<^bsub>vs\<^esub> v = x :=\<^bsub>vs\<^esub> v"
proof -
  from assms(6) have "(VAR - in vs) \<sharp> v" 
    by (auto intro:UNREST_EXPR_subset simp add:in_vars_def)

  with assms show ?thesis
    apply (utp_rel_tac)
    apply (simp add:relcomp_unfold)
    apply (rule Collect_eq_pair_intro)
    apply (safe)
    apply (metis binding_equiv_trans)
    apply (metis binding_equiv_trans)
    apply (simp)
    apply (metis assms(6) utp_expr_tac.EvalP_UNREST_binding_equiv)
    apply (metis assms(6) binding_equiv_idem EvalP_UNREST_binding_equiv)
  done
qed

subsubsection {* Variable Laws *}

theorem VarOpenP_idem:
  "x \<in> D\<^sub>0 \<Longrightarrow> var x ;\<^sub>R var x = var x"
  by (utp_rel_auto_tac)

theorem VarCloseP_idem:
  "x \<in> D\<^sub>0 \<Longrightarrow> end x ;\<^sub>R end x = end x"
  by (utp_rel_auto_tac)

theorem VarOpenP_commute:
  assumes 
    "x \<in> UNDASHED" 
    "y \<in> UNDASHED"
  shows "var x;\<^sub>R var y = var y;\<^sub>R var x"
  using assms
    apply (simp add:VarOpenP_def)
    apply (simp add:assms ExistsP_UNDASHED_expand_SemiR closure)
    apply (metis (hide_lams, no_types) ExistsP_insert insert_commute)
done

theorem VarCloseP_commute:
  assumes
    "x \<in> UNDASHED" "y \<in> UNDASHED" 
  shows "end x;\<^sub>R end y = end y;\<^sub>R end x"
  using assms
    apply (simp add:VarCloseP_def)
    apply (simp add:assms ExistsP_DASHED_expand_SemiR closure)
    apply (metis (hide_lams, no_types) ExistsP_insert insert_commute)
done

lemma [simp]: "REL_VAR - VAR = {}"
  by (simp add:var_simps)

theorem VarOpenP_VarCloseP:
  assumes 
    "x \<in> UNDASHED"
  shows "var x;\<^sub>R end x = II\<^bsub>VAR - {x,x\<acute>}\<^esub>"
  using assms
  apply (simp add:VarOpenP_def VarCloseP_def)
  apply (simp add:ExistsP_UNDASHED_expand_SemiR ExistsP_DASHED_expand_SemiR closure)
  apply (simp add: SkipRA_def)
  apply (metis ExistsP_deatomise doubleton_eq_iff)
done

theorem AssignR_VarCloseP:
  assumes
    "x \<in> UNDASHED" 
    "v \<rhd>\<^sub>e x" 
    "DASHED \<sharp> v"
  shows "x :=\<^sub>R v;\<^sub>R end x = end x"
  using assms
  apply (simp add:AssignR_SemiR_left VarCloseP_def SkipR_as_SkipRA)
  apply (subgoal_tac "UNREST_EXPR {x\<acute>} v")
  apply (simp add: SkipRA_unfold[of x REL_VAR, simplified] usubst closure unrest typing defined)
  apply (subgoal_tac "UNREST {x\<acute>} (II\<^bsub>REL_VAR - {x, x\<acute>}\<^esub>)")
  apply (simp add: ExistsP_AndP_expand1[THEN sym])
  apply (simp add:ExistsP_has_value typing defined unrest)
  apply (rule UNREST_subset)
  apply (rule unrest) back back
  apply (auto intro:unrest UNREST_subset UNREST_EXPR_subset)
done

subsubsection {* Conditional Laws *}

theorem CondR_true[simp]:
  "P \<lhd> true \<rhd> Q = P"
  by (utp_pred_tac)

theorem CondR_false[simp]:
  "P \<lhd> false \<rhd> Q = Q"
  by (utp_pred_tac)

theorem CondR_idem[simp]:
  "P \<lhd> b \<rhd> P = P"
  by (utp_pred_auto_tac)

theorem CondR_sym:
  "P \<lhd> b \<rhd> Q = Q \<lhd> \<not>\<^sub>pb \<rhd> P"
  by (utp_pred_auto_tac)

theorem CondR_assoc:
  "(P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> R = P \<lhd> (b \<and>\<^sub>p c) \<rhd> (Q \<lhd> c \<rhd> R)"
  by (utp_pred_auto_tac)

theorem CondR_distrib:
  "P \<lhd> b \<rhd> (Q \<lhd> c \<rhd> R) = (P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> (P \<lhd> b \<rhd> R)"
  by (utp_pred_auto_tac)

theorem CondR_unreachable_branch:
  "P \<lhd> b \<rhd> (Q \<lhd> b \<rhd> R) = P \<lhd> b \<rhd> R"
  by (utp_pred_auto_tac)

theorem CondR_disj:
  "P \<lhd> b \<rhd> (P \<lhd> c \<rhd> Q) = P \<lhd> b \<or>\<^sub>p c \<rhd> Q"
  by (utp_pred_auto_tac)

theorem CondR_SemiR_distr: 
  assumes 
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION" 
    "r \<in> WF_RELATION" 
    "b \<in> WF_CONDITION"
  shows "(p \<lhd> b \<rhd> q) ;\<^sub>R r = (p ;\<^sub>R r) \<lhd> b \<rhd> (q ;\<^sub>R r)"
  using assms
proof -

  from assms have "b ;\<^sub>R true = b"
    by (simp add: SemiR_TrueP_precond)

  with assms show ?thesis
    by utp_xrel_auto_tac
qed

theorem CondR_true_cond:
  "b \<and>\<^sub>p (P \<lhd> b \<rhd> Q) = b \<and>\<^sub>p P"
  by (utp_pred_auto_tac)

theorem CondR_false_cond:
  "\<not>\<^sub>p b \<and>\<^sub>p (P \<lhd> b \<rhd> Q) = \<not>\<^sub>p b \<and>\<^sub>p Q"
  by (utp_pred_auto_tac)

lemma CondR_AndP_distr:
  "(P \<lhd> b \<rhd> Q) \<and>\<^sub>p R = (P \<and>\<^sub>p R) \<lhd> b \<rhd> (Q \<and>\<^sub>p R)"
  by (utp_pred_auto_tac)

lemma CondR_VarP_aux:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> P \<lhd> $\<^sub>px \<rhd> Q = (P[TrueE/\<^sub>px]) \<lhd> $\<^sub>px \<rhd> (Q[FalseE/\<^sub>px])"
  apply (rule_tac BoolType_aux_var_split_eq_intro[of x])
  apply (simp_all add:usubst typing defined CondR_false CondR_true)
done

subsubsection {* Converse Laws *}

theorem ConvR_invol [simp]: "(p\<^sup>\<smile>)\<^sup>\<smile> = p"
  by (utp_rel_tac)

theorem ConvR_TrueP [simp]: "true\<^sup>\<smile> = true"
  by (simp add:ConvR_def urename)

theorem ConvR_FalseP [simp]: "false\<^sup>\<smile> = false"
  by (simp add:ConvR_def urename)

theorem ConvR_SkipR [simp]: "II\<^sup>\<smile> = II"
  by (utp_rel_tac)

theorem ConvR_SemiR [urename]: "(p;\<^sub>Rq)\<^sup>\<smile> = q\<^sup>\<smile> ;\<^sub>R p\<^sup>\<smile>"
  by (utp_rel_auto_tac)

theorem ConvR_OrP [urename]: "(p \<or>\<^sub>p q)\<^sup>\<smile> = p\<^sup>\<smile> \<or>\<^sub>p q\<^sup>\<smile>"
  by (utp_rel_auto_tac)

theorem ConvR_AndP [urename]: "(p \<and>\<^sub>p q)\<^sup>\<smile> = p\<^sup>\<smile> \<and>\<^sub>p q\<^sup>\<smile>"
  by (utp_rel_auto_tac)

theorem ConvR_NotP [urename]: "(\<not>\<^sub>p p)\<^sup>\<smile> = \<not>\<^sub>p(p\<^sup>\<smile>)"
  by (simp add:ConvR_def urename)

theorem ConvR_VarP_1 [urename]: 
  assumes "x \<in> UNDASHED"
  shows "(VarP x)\<^sup>\<smile> = VarP x\<acute>"
  by (simp add:ConvR_def urename assms)

theorem ConvR_VarP_2 [urename]: 
  assumes "x \<in> UNDASHED"
  shows "(VarP x\<acute>)\<^sup>\<smile> = VarP x"
  by (simp add:ConvR_def urename assms)

subsection {* Additional UNREST theorems *}

lemma WF_RELATION_UNREST_dash2 [unrest]: 
  "P \<in> WF_RELATION \<Longrightarrow> {x\<acute>\<acute>} \<sharp> P"
  apply (simp add:WF_RELATION_def)
  apply (rule UNREST_subset)
  apply (auto simp add:NON_REL_VAR_def)
done

lemma WF_RELATION_UNREST_dash3 [unrest]:
  "P \<in> WF_RELATION \<Longrightarrow> {x\<acute>\<acute>\<acute>} \<sharp> P"
  apply (simp add:WF_RELATION_def)
  apply (rule UNREST_subset)
  apply (auto simp add:NON_REL_VAR_def)
done

lemma EvalP_WF_RELATION_binding_equiv:
  "\<lbrakk> p \<in> WF_RELATION; b1 \<cong> b2 on REL_VAR; \<lbrakk>p\<rbrakk>b1 \<rbrakk> 
    \<Longrightarrow> \<lbrakk>p\<rbrakk>b2"
  apply (auto simp add: WF_RELATION_def)
  apply (rule utp_unrest.EvalP_UNREST_binding_equiv[of "REL_VAR"])
  apply (auto intro:unrest)
done

lemma EvalP_WF_CONDITION_binding_equiv:
  "\<lbrakk> p \<in> WF_CONDITION; b1 \<cong> b2 on UNDASHED; \<lbrakk>p\<rbrakk>b1 \<rbrakk> 
    \<Longrightarrow> \<lbrakk>p\<rbrakk>b2"
  apply (auto simp add: WF_CONDITION_def WF_RELATION_def)
  apply (rule utp_unrest.EvalP_UNREST_binding_equiv[of "UNDASHED"])
  apply (auto intro:unrest)
  apply (subgoal_tac "((VAR - UNDASHED) :: 'a VAR set) = (NON_REL_VAR \<union> DASHED)")
  apply (auto intro:unrest)
done

end