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
"p1 ; (p2 \<or>\<^sub>p p3) = (p1 ; p2) \<or>\<^sub>p (p1 ; p3)"
  by (utp_rel_auto_tac)

theorem SemiR_OrP_distr :
"(p1 \<or>\<^sub>p p2) ; p3 = (p1 ; p3) \<or>\<^sub>p (p2 ; p3)"
  by (utp_rel_auto_tac)

theorem SemiR_SkipR_left [simp]:
"II ; p = p"
  by (utp_rel_auto_tac)

theorem SemiR_SkipR_right [simp]:
"p ; II = p"
  by (utp_rel_auto_tac)

theorem SemiR_FalseP_left [simp]:
"false ; p = false"
  by (utp_rel_auto_tac)

theorem SemiR_FalseP_right [simp]:
"p ; false = false"
  by (utp_rel_auto_tac)

theorem SemiR_assoc :
"p1 ; (p2 ; p3) = (p1 ; p2) ; p3"
  by (utp_rel_auto_tac)

text {* A sequential composition which doesn't mention undashed or dashed variables
        is the same as a conjunction *}

theorem SemiR_equiv_AndP_NON_REL_VAR:
  assumes
    "UNREST REL_VAR p"
    "UNREST REL_VAR q" 
  shows "p ; q = p \<and>\<^sub>p q"
  using assms
  apply (auto simp add:SemiR_def AndP.rep_eq COMPOSABLE_BINDINGS_def)
  apply (rule UNREST_binding_override, simp, simp add:unrest UNREST_subset)
  apply (subgoal_tac "b1 \<oplus>\<^sub>b b2 on NON_REL_VAR = b1")
  apply (rule UNREST_binding_override)
  apply (metis UNDASHED_DASHED_NON_REL_VAR UNREST_binding_override binding_override_minus)
  apply (metis UNREST_subset Un_commute inf_sup_ord(3))
  apply (metis binding_override_equiv)
  apply (rule_tac x="RenameB SS x \<oplus>\<^sub>b x on UNDASHED" in exI)
  apply (rule_tac x="x" in exI)
  apply (auto simp add:urename closure)
  apply (simp add:UNREST_def)
  apply (drule_tac x="x" in bspec, simp)
  apply (drule_tac x="x \<oplus>\<^sub>b RenameB SS x on DASHED" in spec)
  apply (subgoal_tac "x \<oplus>\<^sub>b (x \<oplus>\<^sub>b RenameB SS x on DASHED) on REL_VAR = RenameB SS x \<oplus>\<^sub>b x on UNDASHED")
  apply (simp)
  apply (rule, rule, simp)
  apply (case_tac "xa \<in> UNDASHED")
  apply (simp_all add:urename)
  apply (case_tac "xa \<in> DASHED")
  apply (simp)
  apply (simp add:urename)
  apply (auto simp add:binding_equiv_def urename NON_REL_VAR_def)
done

text {* A condition has true as right identity *}

theorem SemiR_TrueP_precond : 
  assumes "p \<in> WF_CONDITION"
  shows "p ; true = p"
  using assms
  apply (auto simp add:SemiR_def COMPOSABLE_BINDINGS_def TrueP_def UNREST_def WF_CONDITION_def)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="(RenameB SS x) \<oplus>\<^sub>b x on DASHED" in exI)
  apply (auto simp add:RenameB_rep_eq urename binding_equiv_def)
  apply (smt Compl_eq_Diff_UNIV Diff_iff NON_REL_VAR_def SS_ident_app UnCI o_apply override_on_def)
done

text {* A postcondition has true as left identity *}

theorem SemiR_TrueP_postcond :
  assumes "p \<in> WF_POSTCOND"
  shows "true ; p = p"
  using assms
  apply (auto simp add:SemiR_def COMPOSABLE_BINDINGS_def TrueP_def UNREST_def WF_POSTCOND_def)
  apply (drule_tac x="b2" in bspec)
  apply (simp)
  apply (drule_tac x="b1" in spec)
  apply (subgoal_tac "b2 \<oplus>\<^sub>b b1 on UNDASHED = b1 \<oplus>\<^sub>b b2 on DASHED")
  apply (simp)
  apply (rule)
  apply (simp add:binding_equiv_def)
  apply (rule ext)
  apply (case_tac "x \<in> UNDASHED")
  apply (simp_all)
  apply (case_tac "x \<in> DASHED")
  apply (simp)
  apply (subgoal_tac "x \<in> NON_REL_VAR")
  apply (simp)
  apply (auto simp add:NON_REL_VAR_def)[1]
  apply (rule_tac x="(RenameB SS x) \<oplus>\<^sub>b x on UNDASHED" in exI)
  apply (rule_tac x="x" in exI)
  apply (auto)
  apply (rule)
  apply (rule)
  apply (simp add:RenameB_rep_eq urename)
  apply (case_tac "xa \<in> REL_VAR")
  apply (auto simp add:binding_equiv_def urename NON_REL_VAR_def RenameB_rep_eq)
done

(*
lemma PrimeP_rel_closure [closure]:
  "p \<in> WF_RELATION \<Longrightarrow> p\<acute> \<in> WF_RELATION"
  apply (simp add:PrimeP_def WF_RELATION_def)
  apply (rule unrest)
  apply (simp)
  apply (metis SS_NON_REL_VAR_image order_refl)
done
*)

theorem SemiR_AndP_right_precond: 
  assumes 
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION" 
    "c \<in> WF_CONDITION"
  shows "p ; (c \<and>\<^sub>p q) = (p \<and>\<^sub>p c\<acute>) ; q"
  using assms
  by (frule_tac SemiR_TrueP_precond, utp_xrel_auto_tac)

theorem SemiR_AndP_right_postcond: 
  assumes
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION" 
    "c \<in> WF_POSTCOND"
  shows "p ; (q \<and>\<^sub>p c) = (p ; q) \<and>\<^sub>p c"
  using assms
  by (frule_tac SemiR_TrueP_postcond, utp_xrel_auto_tac)

theorem SemiR_AndP_left_postcond: 
  assumes
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION" 
    "c \<in> WF_POSTCOND"
  shows "(p \<and>\<^sub>p c) ; q = p ; (c\<acute> \<and>\<^sub>p q)"
  using assms
  by (frule_tac SemiR_TrueP_postcond, utp_xrel_auto_tac)

theorem SemiR_AndP_left_precond: 
  assumes
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION"  
    "c \<in> WF_CONDITION"
  shows "(c \<and>\<^sub>p p) ; q = c \<and>\<^sub>p (p ; q)"
  using assms
  by (frule_tac SemiR_TrueP_precond, utp_xrel_auto_tac)

theorem SemiR_TrueP_right_precond:
  assumes "P \<in> WF_CONDITION"
  shows "true ; P = P\<acute> ; true"
proof -
  have "true ; P = true ; (P \<and>\<^sub>p true)"
    by simp

  also from assms have "... = P\<acute> ; true"
    by (simp only: SemiR_AndP_right_precond closure, simp)

  ultimately show ?thesis by simp
qed

theorem SemiR_precond_left_zero : 
  assumes 
   "p \<in> WF_CONDITION" 
   "p \<noteq> false"
  shows "true ; p = true"
proof -
  have "true ; p = true ; (p ; true)"
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
  shows "p ; true = true"
proof -
  have "p ; true = (true ; p) ; true"
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
  shows "\<not>\<^sub>p (\<not>\<^sub>p p1 ; true) = p1"
  using assms
  by (metis NotP_NotP NotP_cond_closure SemiR_TrueP_precond)

theorem SemiR_TrueP_TrueP [simp]: 
  "true ; true = true"
  using assms
  by (metis SemiR_TrueP_precond TrueP_cond_closure)

theorem SemiR_cond_idem [simp]:
  assumes "P \<in> WF_CONDITION" 
  shows "P ; P = P"
  using assms
  by (metis SemiR_FalseP_left SemiR_TrueP_precond SemiR_assoc SemiR_precond_left_zero)

theorem SemiR_postcond_idem [simp]:
  assumes "P \<in> WF_POSTCOND"
  shows "P ; P = P"
  using assms
  by (metis SemiR_FalseP_right SemiR_TrueP_postcond SemiR_assoc SemiR_postcond_right_zero)

theorem TrueP_left_annihilator_unique:
  assumes 
    "P \<in> WF_RELATION"
    "P ; true = false"
  shows "P = false"
  using assms
  by (utp_xrel_auto_tac, metis (lifting) prod_caseI2)

theorem TrueP_right_annihilator_unique:
  assumes "P \<in> WF_RELATION"
  shows "true ; P = false \<Longrightarrow> P = false"
  using assms
  by (utp_xrel_auto_tac, metis (lifting) prod_caseI2)

text {* A precondition followed by a postcondition is a conjunction *}

theorem SemiR_COND_POSTCOND:
  assumes 
    "p \<in> WF_CONDITION" "q \<in> WF_POSTCOND"
  shows "p ; q = p \<and>\<^sub>p q"
proof -
  from assms have "p ; true = p" "true ; q = q"
    by (auto dest:SemiR_TrueP_precond SemiR_TrueP_postcond)
  with assms show ?thesis
    by (utp_xrel_auto_tac)
qed

text {* This somewhat odd looking property derives from Relation Algebra. It is used,
        for instance, in the theory of designs. *}

theorem SemiR_TrueP_compl [simp]:
  assumes "P \<in> WF_RELATION"
  shows "\<not>\<^sub>p (P ; true) ; true = \<not>\<^sub>p (P ; true)"
  using assms
  by (utp_xrel_auto_tac)

text {* A single variable can be extracted from a sequential composition and captured
        in an existential *}

theorem SemiR_extract_variable:
  assumes 
    "P \<in> WF_RELATION" 
    "Q \<in> WF_RELATION" 
    "x \<in> UNDASHED"
  shows "P ; Q = (\<exists>\<^sub>p {x\<acute>\<acute>\<acute>}. P[$\<^sub>ex\<acute>\<acute>\<acute>/\<^sub>px\<acute>] ; Q[$\<^sub>ex\<acute>\<acute>\<acute>/\<^sub>px])"
proof -
  have "P ; Q = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>P) \<and>\<^sub>p (SS2\<bullet>Q))"
    by (simp add:assms SemiR_algebraic_rel)

  also have "... = (\<exists>\<^sub>p {x\<acute>\<acute>}. \<exists>\<^sub>p (DASHED_TWICE - {x\<acute>\<acute>}) . (SS1\<bullet>P) \<and>\<^sub>p (SS2\<bullet>Q))"
    by (metis DASHED_dash_DASHED_TWICE ExistsP_insert UNDASHED_dash_DASHED assms(3) insert_Diff)

  (* FIXME: This step really should go through much easier.... *)
  also from assms 
  have "... = (\<exists>\<^sub>p {x\<acute>\<acute>\<acute>}. (\<exists>\<^sub>p DASHED_TWICE - {x\<acute>\<acute>}. ((SS1\<bullet>P) \<and>\<^sub>p (SS2\<bullet>Q)))[$\<^sub>ex\<acute>\<acute>\<acute>/\<^sub>px\<acute>\<acute>])"
    apply (rule_tac trans)
    apply (rule ExistsP_SubstP[of "x\<acute>\<acute>\<acute>"])
    apply (simp_all)
    apply (rule unrest) back
    apply (rule unrest)
    apply (auto intro: unrest closure simp add:urename)
  done

  also from assms 
  have "... = (\<exists>\<^sub>p {x\<acute>\<acute>\<acute>}. (\<exists>\<^sub>p (DASHED_TWICE - {x\<acute>\<acute>}) . ((SubstP (SS1\<bullet>P) ($\<^sub>ex\<acute>\<acute>\<acute>) (x\<acute>\<acute>)) \<and>\<^sub>p (SubstP (SS2\<bullet>Q) ($\<^sub>ex\<acute>\<acute>\<acute>) (x\<acute>\<acute>)))))"
    apply (subgoal_tac "UNREST_EXPR (DASHED_TWICE - {x\<acute>\<acute>}) (VarE x\<acute>\<acute>\<acute>)")
    apply (simp add:usubst closure typing)
    apply (blast intro:unrest)
  done

  also from assms have "... = (\<exists>\<^sub>p {x\<acute>\<acute>\<acute>}. (\<exists>\<^sub>p DASHED_TWICE . ((SubstP (SS1\<bullet>P) (VarE x\<acute>\<acute>\<acute>) (x\<acute>\<acute>)) \<and>\<^sub>p (SubstP (SS2\<bullet>Q) (VarE x\<acute>\<acute>\<acute>) (x\<acute>\<acute>)))))"
    apply (subgoal_tac "UNREST {x\<acute>\<acute>} ((SubstP (SS1\<bullet>P) (VarE x\<acute>\<acute>\<acute>) (x\<acute>\<acute>)) \<and>\<^sub>p (SubstP (SS2\<bullet>Q) (VarE x\<acute>\<acute>\<acute>) (x\<acute>\<acute>)))")
    apply (subgoal_tac "(DASHED_TWICE - {x\<acute>\<acute>}) \<union> {x\<acute>\<acute>} = DASHED_TWICE")
    apply (smt ExistsP_union ExistsP_ident)
    apply (force)
    apply (simp add:unrest typing usubst)
  done

  ultimately show ?thesis using assms
    apply (subgoal_tac "UNREST DASHED_TWICE (SubstP P (VarE (x\<acute>\<acute>\<acute>)) (x\<acute>))")
    apply (subgoal_tac "UNREST DASHED_TWICE (SubstP Q (VarE (x\<acute>\<acute>\<acute>)) (x))")
    apply (subgoal_tac "\<langle>SS1\<rangle>\<^sub>s (x\<acute>\<acute>\<acute>) = x\<acute>\<acute>\<acute>")
    apply (subgoal_tac "\<langle>SS2\<rangle>\<^sub>s (x\<acute>\<acute>\<acute>) = x\<acute>\<acute>\<acute>")
    apply (simp add:SemiR_algebraic urename closure typing defined)
    apply (simp add:urename closure)
    apply (metis SS1_DASHED_TWICE_app SS2_ident_app in_out_UNDASHED_DASHED(1) undash_dash utp_var.not_dash_member_in)
    apply (metis SS1_ident_app UNDASHED_dash_DASHED in_out_UNDASHED_DASHED(4) not_dash_dash_member_out undash_dash undash_eq_dash_contra2)
    apply (rule unrest)
    apply (simp add:typing)
    apply (rule closure, simp)
    apply (rule UNREST_EXPR_VarE[of _ DASHED_TWICE])
    apply (auto)
    apply (rule unrest)
    apply (simp add:typing)
    apply (rule closure, simp)
    apply (rule UNREST_EXPR_VarE[of _ DASHED_TWICE])
    apply (auto)
  done
qed

subsubsection {* Existential Lifting *}

text {* Lifting of exists around sequential composition requires that p1 and p2 are 
        relations and that p1 does use any of the inputs hidden by vs as inputs *}

theorem ExistsP_SemiR_expand1:
  assumes unrests: "UNREST DASHED_TWICE p1" "UNREST DASHED_TWICE p2"
  and     noconn:"UNREST (dash ` in vs) p1"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  shows "p1 ; (\<exists>\<^sub>p vs. p2) = (\<exists>\<^sub>p out vs. (p1 ; p2))"
proof -

  from unrests have "UNREST DASHED_TWICE (\<exists>\<^sub>p vs . p2)"
    by (blast intro:unrest)

  with unrests
  have "p1 ; (\<exists>\<^sub>p vs. p2) = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>(\<exists>\<^sub>p vs . p2)))"
    by (simp add:SemiR_algebraic)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (\<exists>\<^sub>p (SS2 `\<^sub>s vs) . (SS2\<bullet>p2)))"
    by (simp add: RenameP_ExistsP_distr1)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . \<exists>\<^sub>p (SS2 `\<^sub>s vs) . ((SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2)))"
  proof -
    from unrests have "UNREST (SS2 `\<^sub>s vs) (SS1\<bullet>p1)"
    proof -

      have "dash ` (in vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:var_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:var_defs)

      moreover from assms have "UNREST (dash ` dash ` in vs) (SS1\<bullet>p1)"
        by (smt SS1_UNDASHED_DASHED_image UNREST_RenameP_alt Un_empty_left calculation(1) in_dash in_in le_iff_sup out_dash rename_image_def sup.idem)

      moreover from assms have "UNREST (out vs) (SS1\<bullet>p1)"
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

  also from assms have "... = (\<exists>\<^sub>p out vs. (p1 ; p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

theorem ExistsP_SemiR_expand2:
  assumes unrests: "UNREST DASHED_TWICE p1" "UNREST DASHED_TWICE p2"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  and     noconn:"UNREST (undash ` out vs) p2"
  shows "(\<exists>\<^sub>p vs. p1) ; p2 = (\<exists>\<^sub>p in vs. (p1 ; p2))"
proof -

  from unrests have "UNREST DASHED_TWICE (\<exists>\<^sub>p vs . p1)"
    by (blast intro:unrest)

  with unrests
  have "(\<exists>\<^sub>p vs. p1) ; p2 = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>(\<exists>\<^sub>p vs . p1)) \<and>\<^sub>p (SS2\<bullet>p2))"
    by (simp add:SemiR_algebraic closure)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . (\<exists>\<^sub>p (SS1 `\<^sub>s vs) . (SS1\<bullet>p1)) \<and>\<^sub>p (SS2\<bullet>p2))"
    by (metis (lifting) RenameP_ExistsP_distr1)

  also have "... = (\<exists>\<^sub>p DASHED_TWICE . \<exists>\<^sub>p (SS1 `\<^sub>s vs) . ((SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2)))"
  proof -
    from unrests have "UNREST (SS1 `\<^sub>s vs) (SS2\<bullet>p2)"
    proof -

      have "undash ` (out vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:var_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:var_defs)

      moreover from assms have "UNREST (dash ` out vs) (SS2\<bullet>p2)"
        apply (rule_tac ?vs1.0="undash ` out vs" in UNREST_RenameP_alt)
        apply (auto simp add:var_member closure calculation var_simps SS2_simps)
        apply (metis (no_types) DASHED_undash_UNDASHED SS2_UNDASHED_app dash_undash_DASHED rev_image_eqI set_rev_mp utp_var.out_DASHED)
      done

      moreover from assms have "UNREST (in vs) (SS2\<bullet>p2)"
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

  also from assms have "... = (\<exists>\<^sub>p in vs. (p1 ; p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

theorem ExistsP_UNDASHED_expand_SemiR:
  assumes
    "p \<in> WF_RELATION" 
    "q \<in> WF_RELATION" 
    "vs \<subseteq> UNDASHED"
  shows "(\<exists>\<^sub>p vs. p) ; q = (\<exists>\<^sub>p vs. (p ; q))"
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
  shows "p ; (\<exists>\<^sub>p vs. q) = (\<exists>\<^sub>p vs. (p ; q))"
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
    "UNREST DASHED_TWICE p" 
    "UNREST DASHED_TWICE q"
    "UNREST (DASHED - vs1) p" 
    "UNREST (UNDASHED - vs2) q"
    "vs1 \<subseteq> DASHED" 
    "vs2 \<subseteq> UNDASHED"
    "dash ` vs2 \<subseteq> vs1"
  shows "(\<exists>\<^sub>p (vs1 - dash ` vs2). p) ; q = p ; q"
proof -

  let ?A = "dash ` out vs1 - dash ` dash ` in vs2"

  from assms have UNREST: "UNREST DASHED_TWICE (\<exists>\<^sub>p vs1 - dash ` vs2 . p)"
    by (auto intro:unrest)

  hence "(\<exists>\<^sub>p (vs1 - dash ` vs2). p) ; q = 
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
    "UNREST DASHED_TWICE p" 
    "UNREST DASHED_TWICE q"
    "UNREST (DASHED - vs1) p" 
    "UNREST (UNDASHED - vs2) q"
    "vs1 \<subseteq> DASHED" 
    "vs2 \<subseteq> UNDASHED"
    "vs1 \<subseteq> dash ` vs2"
  shows "p ; (\<exists>\<^sub>p (vs2 - undash ` vs1). q) = p ; q"
proof -

  let ?A = "dash ` dash ` in vs2 - (dash ` dash ` in (undash ` vs1) \<union> out (undash ` vs1))"

  from assms have UNREST: "UNREST DASHED_TWICE (\<exists>\<^sub>p vs2 - undash ` vs1 . q)"
    by (auto intro:unrest)

  hence "p ; (\<exists>\<^sub>p (vs2 - undash ` vs1). q) = 
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
    from assms(3) have "UNREST ?A (SS1\<bullet>p)"
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

text {* This property allows conversion of an alphabetised identity into an existential *} 

theorem SemiR_right_ExistsP:
  assumes 
    "p \<in> WF_RELATION" 
    "x \<in> UNDASHED"
  shows "p ; II\<^bsub>(REL_VAR - {x,x\<acute>})\<^esub> = (\<exists>\<^sub>p {x\<acute>}. p)"
  using assms
  apply (subgoal_tac "REL_VAR - (REL_VAR - {x, x\<acute>}) = {x,x\<acute>}")
  apply (auto simp add:SkipRA_def closure unrest ExistsP_SemiR_expand1 var_dist SkipR_ExistsP_out)
done

lemma SubstP_rel_closure [closure]:
  "\<lbrakk> p \<in> WF_RELATION; UNREST_EXPR NON_REL_VAR v; x \<in> REL_VAR; v \<rhd>\<^sub>e x \<rbrakk> 
  \<Longrightarrow> p[v/\<^sub>px] \<in> WF_RELATION"
  by (auto intro:unrest simp add:WF_RELATION_def unrest typing)

theorem SemiR_left_one_point:
  assumes 
    "x \<in> UNDASHED" 
    "P \<in> WF_RELATION" 
    "Q \<in> WF_RELATION" 
    "v \<rhd>\<^sub>e x"
    "UNREST_EXPR (DASHED \<union> NON_REL_VAR) v" 
    "UNREST_EXPR {x} v"
  shows "P ; ($\<^sub>ex ==\<^sub>p v \<and>\<^sub>p Q) = P[v\<acute>/\<^sub>px\<acute>] ; Q[v/\<^sub>px]"
  using assms
  (* This command takes over 15 seconds to complete, really should be optimised.
     The problem is the inclusion of UNREST_EXPR_subset *)
  apply (simp add:unrest urename closure typing defined UNREST_EXPR_subset evalrx evale relcomp_unfold)
  apply (auto)
  apply (metis DestXRelB_inverse binding_upd_triv xbinding_upd_def)
  apply (rule_tac x="ya(x :=\<^sub>x \<lbrakk>v\<rbrakk>\<^sub>e\<langle>ya\<rangle>\<^sub>x)" in exI)
  apply (simp add:evale)
done

lemma xbinding_upd_refl [simp]: 
  "x \<in> UNDASHED \<Longrightarrow> b(x :=\<^sub>x \<langle>\<langle>b\<rangle>\<^sub>x\<rangle>\<^sub>b x) = b"
  by (auto simp add:typing defined)

theorem SemiR_right_one_point:
  assumes 
    "x \<in> UNDASHED" 
    "P \<in> WF_RELATION" 
    "Q \<in> WF_RELATION" 
    "v \<rhd>\<^sub>e x"
    "UNREST_EXPR (DASHED \<union> NON_REL_VAR) v" 
    "UNREST_EXPR {x} v"
  shows "(P \<and>\<^sub>p $\<^sub>ex\<acute> ==\<^sub>p v\<acute>) ; Q = P[v\<acute>/\<^sub>px\<acute>] ; Q[v/\<^sub>px]"
  using assms
  apply (simp add:unrest urename closure typing defined UNREST_EXPR_subset evalrx evale)
  apply (subgoal_tac "$\<^sub>ex\<acute> ==\<^sub>p v\<acute> = ($\<^sub>ex)\<acute> ==\<^sub>p v\<acute>")
  apply (simp add:unrest closure typing defined UNREST_EXPR_subset evalrx evale relcomp_unfold)
  defer
  apply (utp_pred_tac, simp add:urename)
  apply (auto)
  apply (rule_tac x="ya" in exI)
  apply (drule sym) back
  apply (simp add:evale typing)
  apply (rule_tac x="ya(x :=\<^sub>x \<lbrakk>v\<rbrakk>\<^sub>e\<langle>ya\<rangle>\<^sub>x)" in exI)
  apply (simp add:evale)
done

theorem SemiR_right_one_point_alt:
  assumes 
    "x \<in> DASHED" 
    "P \<in> WF_RELATION" 
    "Q \<in> WF_RELATION" 
    "v \<rhd>\<^sub>e x"
    "UNREST_EXPR (UNDASHED \<union> NON_REL_VAR) v" 
    "UNREST_EXPR {x} v"
  shows "(P \<and>\<^sub>p $\<^sub>ex ==\<^sub>p v) ; Q = P[v/\<^sub>px] ; Q[v\<acute>/\<^sub>pundash x]"
proof -

  from assms have u1:"UNREST_EXPR (DASHED \<union> NON_REL_VAR) (v\<acute>)"
    by (simp add:urename unrest)

  from assms have u2:"UNREST_EXPR {undash x} (v\<acute>)"
    by (simp add:urename unrest)

  thus ?thesis
    apply (insert SemiR_right_one_point[of "undash x" P Q "v\<acute>"])
    apply (simp add:urename closure assms unrest typing u1 u2)
  done
qed

subsubsection {* Alphabetised Skip laws *}

theorem SemiR_SkipRA_right :
  assumes 
  "UNREST (DASHED - out vs) p"
  "UNREST (dash ` (UNDASHED - in vs)) p"
  "UNREST DASHED_TWICE p" 
  "vs \<subseteq> UNDASHED \<union> DASHED"
  shows 
  "p ; II\<^bsub>vs\<^esub> = p"
proof -
  have "UNREST DASHED_TWICE II"
    by (auto simp add:SkipR_def closure UNREST_def)

  moreover from assms have "UNDASHED - in vs =  in (UNDASHED \<union> DASHED - vs)"
    by (auto simp add:var_simps var_defs)

  moreover from assms have "out (UNDASHED \<union> DASHED - vs) = DASHED - out vs "
    by (auto simp add:var_simps var_defs)

  moreover have "(UNDASHED \<union> DASHED) - vs \<subseteq> (UNDASHED \<union> DASHED)"
    by force

  moreover from assms have "p ; II = p"
    by (utp_rel_auto_tac)

  ultimately show ?thesis using assms
    by (metis (lifting) ExistsP_SemiR_expand1 ExistsP_ident SkipRA.rep_eq)
qed

theorem SemiR_SkipRA_left :
  assumes 
  "UNREST (UNDASHED - in vs) p"
  "UNREST (undash ` (DASHED - out vs)) p"
  "UNREST DASHED_TWICE p" 
  "vs \<subseteq> UNDASHED \<union> DASHED"
  shows 
  "II\<^bsub>vs\<^esub> ; p = p"
proof -
  have "UNREST DASHED_TWICE II"
    by (auto simp add:SkipR_def closure UNREST_def)

  moreover have "(UNDASHED \<union> DASHED) - vs \<subseteq> (UNDASHED \<union> DASHED)"
    by force

  moreover from assms have "DASHED - out vs = out (UNDASHED \<union> DASHED - vs)"
    by (auto simp add:var_simps var_defs)

  moreover from assms have "in (UNDASHED \<union> DASHED - vs) = UNDASHED - in vs "
    by (auto simp add:var_simps var_defs)

  moreover from assms have "II ; p = p"
    by (utp_rel_auto_tac)

  ultimately show ?thesis using assms
    by (metis (lifting) ExistsP_SemiR_expand2 ExistsP_ident SkipRA.rep_eq)
qed

theorem SkipRA_left_unit:
  assumes 
    "P \<in> WF_RELATION" 
    "vs \<subseteq> REL_VAR" 
    "UNREST (UNDASHED - in vs) P"
    "HOMOGENEOUS vs"
  shows "II\<^bsub>vs\<^esub> ; P = P"
  apply (rule_tac SemiR_SkipRA_left)
  apply (simp_all add:assms unrest closure var_dist)
done

theorem SkipRA_right_unit:
  assumes 
    "P \<in> WF_RELATION" 
    "vs \<subseteq> REL_VAR" 
    "UNREST (DASHED - out vs) P"
    "HOMOGENEOUS vs"
  shows "P ; II\<^bsub>vs\<^esub> = P"
  apply (rule_tac SemiR_SkipRA_right)
  apply (simp_all add:assms unrest closure var_dist)
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

theorem SkipRA_compose [simp]:
  assumes 
    "HOMOGENEOUS vs1"
    "HOMOGENEOUS vs2" 
    "vs1 \<subseteq> REL_VAR" 
    "vs2 \<subseteq> REL_VAR"
  shows "II\<^bsub>vs1\<^esub> ; II\<^bsub>vs2\<^esub> = II\<^bsub>vs1 \<inter> vs2\<^esub>"
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
    "UNREST_EXPR DASHED e"
  shows "x :=\<^sub>R e ; p = p[e/\<^sub>px]"
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
    "UNREST_EXPR (UNDASHED \<union> DASHED - vs) v" 
    "v \<rhd>\<^sub>e x"
  shows "x :=\<^bsub>vs\<^esub> v = $\<^sub>ex\<acute> ==\<^sub>p v \<and>\<^sub>p II\<^bsub>(vs - {x,x\<acute>})\<^esub>"
using assms
proof (simp add:SkipRA_def AssignRA_def AssignR_alt_def)
  from assms have "REL_VAR - (vs - {x, x\<acute>}) = (REL_VAR - vs) \<union> {x, x\<acute>}"
    by (auto)

  hence "(\<exists>\<^sub>p REL_VAR - (vs - {x, x\<acute>}) . II) = (\<exists>\<^sub>p REL_VAR - vs. \<exists>\<^sub>p {x, x\<acute>} . II)"
    by (metis (lifting) ExistsP_union)

  moreover from assms have "UNREST (REL_VAR - vs) ($\<^sub>ex\<acute> ==\<^sub>p v)"
    by (rule_tac unrest, auto intro:unrest)

  ultimately show "(\<exists>\<^sub>p REL_VAR - vs . $\<^sub>ex\<acute> ==\<^sub>p v \<and>\<^sub>p (\<exists>\<^sub>p {x, x\<acute>} . II)) =
                    $\<^sub>ex\<acute> ==\<^sub>p v \<and>\<^sub>p (\<exists>\<^sub>p insert x (insert x\<acute> (REL_VAR - vs)) . II)"
    by (smt ExistsP_AndP_expand2 ExistsP_union Un_empty_right Un_insert_right union_minus)
qed

theorem AssignRA_SemiR_left:
  assumes 
    "x \<in> UNDASHED" 
    "x \<in> vs" 
    "e \<rhd>\<^sub>e x" 
    "HOMOGENEOUS vs" 
    "vs \<subseteq> UNDASHED \<union> DASHED"
    "UNREST (VAR - vs) p" 
    "UNREST_EXPR (VAR - in vs) e"
  shows "(x :=\<^bsub>vs\<^esub> e ; p) = p[e/\<^sub>px]"
proof -

  from assms have "UNREST DASHED_TWICE (x :=\<^sub>R e)" 
    apply (rule_tac UNREST_subset)
    apply (rule unrest)
    apply (auto)
    apply (rule UNREST_EXPR_subset)
    apply (auto)
  done

  moreover from assms have "UNREST DASHED_TWICE p" 
    by (rule_tac UNREST_subset, auto intro:unrest)

  moreover from assms have 
    "UNDASHED \<union> DASHED - vs \<subseteq> UNDASHED \<union> DASHED" and
    "UNREST (undash ` out (UNDASHED \<union> DASHED - vs)) p"
    "UNREST_EXPR DASHED e"
    apply (auto intro:unrest)
    apply (rule_tac UNREST_subset)
    apply (simp)
    apply (simp add:var_dist)
    apply (force)
    apply (rule UNREST_EXPR_subset)
    apply (simp)
    apply (force)
  done

  moreover from assms have "UNREST (in (UNDASHED \<union> DASHED - vs)) (p[e/\<^sub>px])"
    apply (rule_tac UNREST_subset[of "(VAR - vs) \<inter> (VAR - in vs)"])
    apply (rule_tac unrest)
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

subsubsection {* Variable Laws *}

theorem VarOpenP_commute:
  assumes 
    "x \<in> UNDASHED" 
    "y \<in> UNDASHED"
  shows "var x; var y = var y; var x"
  using assms
    apply (simp add:VarOpenP_def)
    apply (simp add:assms ExistsP_UNDASHED_expand_SemiR closure)
    apply (metis (hide_lams, no_types) ExistsP_insert insert_commute)
done

theorem VarCloseP_commute:
  assumes
    "x \<in> UNDASHED" "y \<in> UNDASHED" 
  shows "end x; end y = end y; end x"
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
  shows "var x; end x = II\<^bsub>VAR - {x,x\<acute>}\<^esub>"
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
    "UNREST_EXPR DASHED v"
  shows "x :=\<^sub>R v; end x = end x"
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

theorem CondR_true:
  "P \<lhd> true \<rhd> Q = P"
  by (utp_pred_tac)

theorem CondR_false:
  "P \<lhd> false \<rhd> Q = Q"
  by (utp_pred_tac)

theorem CondR_idem:
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
  shows "(p \<lhd> b \<rhd> q) ; r = (p ; r) \<lhd> b \<rhd> (q ; r)"
  using assms
proof -

  from assms have "b ; true = b"
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

theorem ConvR_SemiR [urename]: "(p;q)\<^sup>\<smile> = q\<^sup>\<smile> ; p\<^sup>\<smile>"
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
  "P \<in> WF_RELATION \<Longrightarrow> UNREST {x\<acute>\<acute>} P"
  apply (simp add:WF_RELATION_def)
  apply (rule UNREST_subset)
  apply (auto simp add:NON_REL_VAR_def)
done

lemma WF_RELATION_UNREST_dash3 [unrest]:
  "P \<in> WF_RELATION \<Longrightarrow> UNREST {x\<acute>\<acute>\<acute>} P"
  apply (simp add:WF_RELATION_def)
  apply (rule UNREST_subset)
  apply (auto simp add:NON_REL_VAR_def)
done

end