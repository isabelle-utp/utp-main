(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_laws.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Albegraic Laws *}

theory utp_laws
imports utp_pred utp_rel utp_subst "../alpha/utp_alphabet"
  "../tactics/utp_pred_tac"
  "../tactics/utp_rel_tac"
begin

context PRED
begin

lemma IffP_eq_intro[intro]:
"\<lbrakk>p \<in> WF_PREDICATE; q \<in> WF_PREDICATE; taut (p \<Leftrightarrow>p q)\<rbrakk> \<Longrightarrow> p = q"
  by (utp_pred_auto_tac)

subsection {* Quantifiers *}

theorem ExistsP_ident :
"\<lbrakk>p \<in> WF_PREDICATE;
 UNREST vs p\<rbrakk> \<Longrightarrow>
 (\<exists>p vs . p) = p"
apply (simp add: ExistsP_def)
apply (safe)
apply (simp add: UNREST_binding_override)
apply (rule_tac x = "x" in exI)
apply (rule_tac x = "x" in exI)
apply (simp)
done

theorem ForallP_ident :
"\<lbrakk>p \<in> WF_PREDICATE;
 UNREST vs p\<rbrakk> \<Longrightarrow>
 (\<forall>p vs . p) = p"
apply (simp add: ForallP_def)
apply (simp add: ExistsP_ident UNREST_NotP closure)
apply (simp add: NotP_NotP closure)
done

theorem ExistsP_union :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p vs1 \<union> vs2 . p) = (\<exists>p vs1 . \<exists>p vs2 . p)"
apply (utp_pred_tac)
apply (safe)
apply (rule_tac x = "b'" in bexI)
apply (rule_tac x = "b'" in bexI)
apply (simp)+
apply (simp add: override_on_assoc)
apply (rule_tac x = "b' \<oplus> b'a on vs2" in bexI)
apply (assumption)
apply (simp add: closure)
done

theorem ForallP_union :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>p vs1 \<union> vs2 . p) = (\<forall>p vs1 . \<forall>p vs2 . p)"
apply (simp add: ForallP_def closure)
apply (simp add: ExistsP_union UNREST_NotP closure)
apply (simp add: NotP_NotP closure)
done

subsection {* Substitution *}

subsubsection {* Distribution Theorems *}

theorem SubstP_NotP_distr :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (\<not>p p)[ss] = \<not>p p[ss]"
apply (utp_pred_auto_tac)
done

theorem SubstP_AndP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<and>p p2)[ss] = p1[ss] \<and>p p2[ss]"
apply (utp_pred_auto_tac)
done

theorem SubstP_OrP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<or>p p2)[ss] = p1[ss] \<or>p p2[ss]"
apply (utp_pred_auto_tac)
done

theorem SubstP_ImpliesP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<Rightarrow>p p2)[ss] = p1[ss] \<Rightarrow>p p2[ss]"
apply (utp_pred_auto_tac)
done

theorem SubstP_IffP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (p1 \<Leftrightarrow>p p2)[ss] = p1[ss] \<Leftrightarrow>p p2[ss]"
apply (utp_pred_auto_tac)
done

theorem SubstP_ExistsP_distr1 :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (\<exists>p vs . p)[ss] = (\<exists>p ss ` vs . p[ss])"
apply (utp_pred_tac)
apply (safe)
apply (rule_tac x="SubstB ss b'" in bexI)
apply (simp add:SubstB_override_distr1 closure)
apply (simp add:closure)
apply (rule_tac x="SubstB (inv ss) b'" in bexI)
apply (simp add:SubstB_override_distr1 closure)
apply (simp add:closure)
done

theorem SubstP_ExistsP_distr2 :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<exists>p vs2 . p)[ss] = (\<exists>p vs2 . p[ss])"
  by (simp add:SubstP_ExistsP_distr1 closure)

theorem SubstP_ForallP_distr :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<forall>p vs2 . p)[ss] = (\<forall>p vs2 . p[ss])"
apply (simp add: ForallP_def closure)
apply (simp add: SubstP_ExistsP_distr2 SubstP_NotP_distr closure)
done

theorem SubstP_ClosureP :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 [p[ss]]p = [p]p"
apply (utp_pred_tac)
apply (safe)
apply (drule_tac x = "SubstB ss x" in bspec)
apply (simp_all add: closure)
done

subsubsection {* Other substitution laws *}

theorem SubstP_UNREST [simp]:
"\<lbrakk> p \<in> WF_PREDICATE; UNREST vs p; ss \<in> VAR_SUBST_ON vs \<rbrakk> \<Longrightarrow> p[ss] = p"
  apply (utp_pred_tac)
  apply (rule ballI)
  apply (frule VAR_SUBST_ON_inv)
  apply (simp add:VAR_SUBST_ON_def)
  apply (clarify)
  apply (simp add:SubstB_def EvalP_def UNREST_def)
  apply (rule iffI)
  apply (subgoal_tac "(b \<circ> ss) \<oplus> b on vs = b")
  apply (drule_tac x="b \<circ> ss" in bspec, simp)
  apply (drule_tac x="b" in bspec, simp)
  apply (simp)
  apply (force simp add:override_on_def) 
  apply (subgoal_tac "b \<oplus> (b \<circ> ss) on vs = b \<circ> ss")
  apply (drule_tac x="b" in bspec, simp)
  apply (drule_tac x="b \<circ> ss" in bspec)
  apply (metis VAR_SUBST_WF_BINDING WF_BINDING_member)
  apply (simp)
  apply (force simp add:override_on_def) 
done

subsection {* Proof Experiments *}

text {*
  The following proof illustrates how we use a mixture of algebraic laws and
  the proof strategy for predicates to proof more complex properties. For now
  the strategy alone is not powerful enough to prove the theorem by itself.
*}

theorem SubstP_invariant_taut :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 taut [p1 \<Leftrightarrow>p p2]p \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]p"
apply (utp_pred_auto_tac)
oops

theorem SubstP_invariant_taut :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 taut [p1 \<Leftrightarrow>p p2]p \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]p"
apply (subgoal_tac "p1[ss] \<Leftrightarrow>p p2[ss] = (p1 \<Leftrightarrow>p p2)[ss]")
apply (simp)
apply (simp add: SubstP_ClosureP closure)
apply (utp_pred_tac)
apply (simp add: SubstP_IffP_distr)
done

theorem ExistsP_OrP_expand:
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p vs. p1 \<or>p p2) = (\<exists>p vs. p1) \<or>p (\<exists>p vs. p2)"
  by (utp_pred_auto_tac)

theorem ExistsP_AndP_expand1:
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 (\<exists>p vs. p1) \<and>p p2 = (\<exists>p vs. (p1 \<and>p p2))"
  by (utp_pred_tac, metis EvalP_ExistsP EvalP_def ExistsP_ident UNREST_binding_override)


  theorem ExistsP_AndP_expand2:
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p1\<rbrakk> \<Longrightarrow>
 p1 \<and>p (\<exists>p vs. p2) = (\<exists>p vs. (p1 \<and>p p2))"
  by (utp_pred_tac, metis EvalP_ExistsP EvalP_def ExistsP_ident UNREST_binding_override)

text {* Lifting of exists around sequential composition requires that p1 and p2 are relations 
        and that p1 does use any of the inputs hidden by vs as inputs *}
theorem ExistsP_SemiP_expand1:
  assumes wfpreds: "p1 \<in> WF_PREDICATE" "p2 \<in> WF_PREDICATE"
  and     unrests: "UNREST DASHED_TWICE p1" "UNREST DASHED_TWICE p2"
  and     noconn:"UNREST (dash ` in vs) p1"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  shows "p1 ; (\<exists>p vs. p2) = (\<exists>p out vs. (p1 ; p2))"
proof -

  from unrests wfpreds have "UNREST DASHED_TWICE (\<exists>p vs . p2)"
    by (blast intro:unrest)

  with unrests wfpreds
  have "p1 ; (\<exists>p vs. p2) = (\<exists>p DASHED_TWICE . p1[SS1] \<and>p (\<exists>p vs . p2)[SS2])"
    by (simp add:SemiR_algebraic closure)

  also have "... = (\<exists>p DASHED_TWICE . p1[SS1] \<and>p (\<exists>p (SS2 ` vs) . p2[SS2]))"
    by (metis (lifting) SS2_VAR_SUBST SubstP_ExistsP_distr1 wfpreds)

  also have "... = (\<exists>p DASHED_TWICE . \<exists>p (SS2 ` vs) . (p1[SS1] \<and>p p2[SS2]))"
  proof -
    from unrests wfpreds have "UNREST (SS2 ` vs) p1[SS1]"
    proof -

      have "dash ` (in vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:alphabet_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:alphabet_defs)

      moreover from assms have "UNREST (dash ` dash ` in vs) p1[SS1]"
        by (force intro:UNREST_SubstP_alt simp add: alphabet_member closure calculation alphabet_simps SS1_simps)        

      moreover from assms have "UNREST (out vs) p1[SS1]"
        apply (rule_tac ?vs1.0="dash ` out vs" in UNREST_SubstP_alt)
        apply (simp_all add:closure calculation)
        apply (force intro:  UNREST_subset simp add:alphabet_defs)
        apply (auto simp add:image_def SS1_simps closure alphabet_defs)
      done

      ultimately show ?thesis using assms
        by (force intro:UNREST_union closure simp add: SS2_simps)
    qed

    thus ?thesis
      by (metis ExistsP_AndP_expand2 SS1_VAR_SUBST SS2_VAR_SUBST SubstP_closure assms)
  qed

  also from assms have "... = (\<exists>p out vs. \<exists>p DASHED_TWICE . p1[SS1] \<and>p p2[SS2])"
  proof -
    have "DASHED_TWICE \<union> dash ` dash ` (in vs) = DASHED_TWICE"
      by (force simp add:alphabet_defs)

    thus ?thesis using assms
      apply (simp add:SS2_simps)
      apply (simp add:ExistsP_union closure)
      apply (metis AndP_closure ExistsP_closure ExistsP_union SS1_VAR_SUBST SS2_VAR_SUBST SubstP_closure Un_commute in_alphabet_def)
    done
  qed

  also from assms have "... = (\<exists>p out vs. (p1 ; p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

theorem ExistsP_SemiP_expand2:
  assumes wfpreds: "p1 \<in> WF_PREDICATE" "p2 \<in> WF_PREDICATE"
  and     unrests: "UNREST DASHED_TWICE p1" "UNREST DASHED_TWICE p2"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  and     noconn:"UNREST (undash ` out vs) p2"
  shows "(\<exists>p vs. p1) ; p2 = (\<exists>p in vs. (p1 ; p2))"
proof -

  from unrests wfpreds have "UNREST DASHED_TWICE (\<exists>p vs . p1)"
    by (blast intro:unrest)

  with unrests wfpreds
  have "(\<exists>p vs. p1) ; p2 = (\<exists>p DASHED_TWICE . (\<exists>p vs . p1)[SS1] \<and>p p2[SS2])"
    by (simp add:SemiR_algebraic closure)

  also have "... = (\<exists>p DASHED_TWICE . (\<exists>p (SS1 ` vs) . p1[SS1]) \<and>p p2[SS2])"
    by (metis (lifting) SS1_VAR_SUBST SubstP_ExistsP_distr1 wfpreds)

  also have "... = (\<exists>p DASHED_TWICE . \<exists>p (SS1 ` vs) . (p1[SS1] \<and>p p2[SS2]))"
  proof -
    from unrests wfpreds have "UNREST (SS1 ` vs) p2[SS2]"
    proof -

      have "undash ` (out vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:alphabet_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:alphabet_defs)

      moreover from assms have "UNREST (dash ` out vs) p2[SS2]"
        apply (rule_tac ?vs1.0="undash ` out vs" in UNREST_SubstP_alt)
        apply (simp_all add:alphabet_member closure calculation alphabet_simps SS2_simps)
      done

      moreover from assms have "UNREST (in vs) p2[SS2]"
        apply (rule_tac ?vs1.0="dash ` dash ` in vs" in UNREST_SubstP_alt)
        apply (simp_all add:closure calculation)
        apply (force intro:  UNREST_subset simp add:alphabet_defs)
        apply (auto simp add:closure alphabet_defs image_def)
        apply (rule_tac x="dash (dash x)" in exI)
        apply (auto simp add:SS2_simps)
      done

      ultimately show ?thesis using assms
        by (force intro:UNREST_union closure simp add:SS1_simps)
    qed

    thus ?thesis
      by (metis ExistsP_AndP_expand1 SS1_VAR_SUBST SS2_VAR_SUBST SubstP_closure assms)
  qed

  also from assms have "... = (\<exists>p in vs. \<exists>p DASHED_TWICE . p1[SS1] \<and>p p2[SS2])"
  proof -
    have "dash ` (out vs) \<union> DASHED_TWICE = DASHED_TWICE"
      by (force simp add:alphabet_defs)

    thus ?thesis using assms
      apply (simp add:SS1_simps)
      apply (simp add:ExistsP_union closure)
      apply (smt AndP_closure ExistsP_union SS1_VAR_SUBST SS2_VAR_SUBST SubstP_closure Un_assoc sup.commute)
    done
  qed

  also from assms have "... = (\<exists>p in vs. (p1 ; p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

(* Note that assumption assumption 4 is automatic under a homogeneous alphabet *)
theorem SemiP_SkipRA_right :
  assumes 
  "p \<in> WF_PREDICATE"
  "UNREST (DASHED - out vs) p"
  "UNREST (dash ` (UNDASHED - in vs)) p"
  "UNREST DASHED_TWICE p" 
  "vs \<subseteq> UNDASHED \<union> DASHED"
  shows 
  "p ; II vs = p"
proof -
  have "UNREST DASHED_TWICE II"
    by (auto simp add:SkipR_def closure UNREST_def)

  moreover from assms have "UNDASHED - in vs =  in (UNDASHED \<union> DASHED - vs)"
    by (auto simp add:alphabet_simps alphabet_defs)

  moreover from assms have "out (UNDASHED \<union> DASHED - vs) = DASHED - out vs "
    by (auto simp add:alphabet_simps alphabet_defs)

  moreover have "(UNDASHED \<union> DASHED) - vs \<subseteq> (UNDASHED \<union> DASHED)"
    by force

  moreover from assms have "p ; II = p"
    by (utp_rel_auto_tac)

  ultimately show ?thesis using assms
    by (simp add:SkipRA_def ExistsP_SemiP_expand1 closure ExistsP_ident)
qed

theorem SemiP_SkipRA_left :
  assumes 
  "p \<in> WF_PREDICATE"
  "UNREST (UNDASHED - in vs) p"
  "UNREST (undash ` (DASHED - out vs)) p"
  "UNREST DASHED_TWICE p" 
  "vs \<subseteq> UNDASHED \<union> DASHED"
  shows 
  "II vs ; p = p"
proof -
  have "UNREST DASHED_TWICE II"
    by (auto simp add:SkipR_def closure UNREST_def)

  moreover have "(UNDASHED \<union> DASHED) - vs \<subseteq> (UNDASHED \<union> DASHED)"
    by force

  moreover from assms have "DASHED - out vs = out (UNDASHED \<union> DASHED - vs)"
    by (auto simp add:alphabet_simps alphabet_defs)

  moreover from assms have "in (UNDASHED \<union> DASHED - vs) = UNDASHED - in vs "
    by (auto simp add:alphabet_simps alphabet_defs)

  moreover from assms have "II ; p = p"
    by (utp_rel_auto_tac)

  ultimately show ?thesis using assms
    by (simp add:SkipRA_def ExistsP_SemiP_expand2 ExistsP_ident closure)
qed

theorem SkipRA_unfold :
  assumes "x \<in> vs" "dash x \<in> vs" "x \<in> UNDASHED" "HOMOGENEOUS vs"
  shows "II vs = VarE (dash x) ==p VarE x \<and>p II (vs - {x,dash x})"
proof -

  have "(UNDASHED \<union> DASHED - vs) \<inter> (UNDASHED \<union> DASHED - (vs - {x, dash x})) = UNDASHED \<union> DASHED - vs"
    by (force)


  (* The proof below proceeds by showing that any variable v is identified by both sides
     of the goal. The are three cases of v:
     1) v = x
     2) v \<noteq> x and v \<in> vs
     3) v \<noteq> x and v \<notin> vs
  *)

  with assms show ?thesis
    apply (simp add:SkipRA_def)
    apply (utp_pred_tac, utp_expr_tac)
    apply (safe)
    (* Subgoal 1 *)
    apply (force)
    (* Subgoal 2 *)
    apply (rule_tac x="b \<oplus> b' on UNDASHED \<union> DASHED - vs" in bexI)
    apply (simp_all add:closure)
    (* Subgoal 3 *)
    apply (rule_tac x="b'" in bexI)
    apply (rule ballI, simp_all)
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

theorem SkipRA_assign :
  assumes "x \<in> vs" "dash x \<in> vs" "x \<in> UNDASHED" "HOMOGENEOUS vs"
  shows "II vs = x :=p\<^bsub>vs\<^esub> VarE x"
  by (simp add:AssignR_def SkipRA_unfold assms)

theorem SemiR_OrR_distl :
"\<lbrakk>r1 \<in> WF_PREDICATE;
 r2 \<in> WF_PREDICATE;
 r3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 r1 ; (r2 \<or>p r3) = (r1 ; r2) \<or>p (r1 ; r3)"
  by utp_rel_tac

theorem SemiR_OrR_distr :
"\<lbrakk>r1 \<in> WF_PREDICATE;
 r2 \<in> WF_PREDICATE;
 r3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (r1 \<or>p r2) ; r3 = (r1 ; r3) \<or>p (r2 ; r3)"
  by utp_rel_tac

theorem SemiR_CondR_distr:
  assumes 
    "p \<in> WF_PREDICATE" "q \<in> WF_PREDICATE" "r \<in> WF_PREDICATE" "b \<in> WF_PREDICATE"
    "UNREST DASHED_TWICE p" 
    "UNREST DASHED_TWICE q" 
    "UNREST DASHED_TWICE r" 
    "UNREST DASHED_TWICE b"
    "UNREST DASHED b"
  shows "(p \<triangleleft> b \<triangleright> q) ; r = (p ; r) \<triangleleft> b \<triangleright> (q ; r)"
proof -
  from assms have "UNREST DASHED_TWICE (p \<triangleleft> b \<triangleright> q)"
    by (simp add:CondR_def, auto intro:unrest closure)

  with assms
  have "(p \<triangleleft> b \<triangleright> q) ; r = (\<exists>p DASHED_TWICE . (b \<and>p p \<or>p \<not>p b \<and>p q)[SS1] \<and>p r[SS2])" 
    by (simp add:SemiR_algebraic CondR_def closure)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b[SS1] \<and>p p[SS1] \<or>p \<not>p b[SS1] \<and>p q[SS1]) \<and>p r[SS2])"
    by (utp_pred_auto_tac)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b \<and>p p[SS1] \<or>p \<not>p b \<and>p q[SS1]) \<and>p r[SS2])"
    by (metis ExistsP_ident SS1_VAR_SUBST_ON SubstP_UNREST UNREST_ExistsP)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b \<and>p p[SS1] \<and>p r[SS2] \<or>p \<not>p b \<and>p q[SS1] \<and>p r[SS2]))"
    by (utp_pred_auto_tac)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b \<and>p p[SS1] \<and>p r[SS2])) \<or>p (\<exists>p DASHED_TWICE . (\<not>p b \<and>p q[SS1] \<and>p r[SS2]))"
    by (utp_pred_auto_tac)

  also from assms
  have "... = b \<and>p (\<exists>p DASHED_TWICE . (p[SS1] \<and>p r[SS2])) \<or>p \<not>p b \<and>p (\<exists>p DASHED_TWICE . (q[SS1] \<and>p r[SS2]))"
  proof -
    from assms have "UNREST DASHED_TWICE (\<not>p b)"
      by (blast intro:unrest)
      
    with assms show ?thesis
      by (simp add: ExistsP_AndP_expand2[THEN sym] closure)
  qed
    
  also from assms have "... = (p ; r) \<triangleleft> b \<triangleright> (q ; r)"
    by (simp add:SemiR_algebraic CondR_def closure)

  ultimately show ?thesis
    by simp

qed

end
end