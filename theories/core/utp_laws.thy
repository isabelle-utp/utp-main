(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_laws.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Algebraic Laws *}

theory utp_laws
imports utp_pred utp_rel utp_rename "../alpha/utp_alphabet"
  "../tactics/utp_pred_tac"
  "../tactics/utp_rel_tac"
  "../tactics/utp_expr_tac"
begin

lemma IffP_eq_intro[intro]:
"taut (p \<Leftrightarrow>p q) \<Longrightarrow> p = q"
  by (utp_pred_auto_tac)

subsection {* Quantifiers *}

theorem ExistsP_ident :
"\<lbrakk>UNREST vs p\<rbrakk> \<Longrightarrow>
 (\<exists>p vs . p) = p"
apply (simp add: ExistsP_def)
apply (safe)
apply (auto simp add: UNREST_binding_override)
apply (rule_tac x = "x" in exI)
apply (simp)
apply (rule_tac x = "x" in exI)
apply (simp)
done

theorem ForallP_ident :
"\<lbrakk>UNREST vs p\<rbrakk> \<Longrightarrow>
 (\<forall>p vs . p) = p"
apply (simp add: ForallP_def)
apply (simp add: ExistsP_ident UNREST_NotP closure)
apply (simp add: NotP_NotP closure)
done

theorem ExistsP_union :
"(\<exists>p vs1 \<union> vs2 . p) = (\<exists>p vs1 . \<exists>p vs2 . p)"
apply (utp_pred_tac)
apply (safe)
apply (rule_tac x = "b'" in exI)
apply (rule_tac x = "b'" in exI)
apply (simp)+
apply (rule_tac x = "b' \<oplus>\<^sub>b b'a on vs2" in exI)
apply (simp add: binding_override_assoc)
done

theorem ForallP_union :
"(\<forall>p vs1 \<union> vs2 . p) = (\<forall>p vs1 . \<forall>p vs2 . p)"
apply (simp add: ForallP_def closure)
apply (simp add: ExistsP_union UNREST_NotP closure)
apply (simp add: NotP_NotP closure)
done

subsection {* Renaming *}

subsubsection {* Distribution Theorems *}

theorem RenameP_NotP_distr [urename]:
"(\<not>p p)[ss] = \<not>p p[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_AndP_distr [urename]:
"(p1 \<and>p p2)[ss] = p1[ss] \<and>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_OrP_distr [urename]:
"(p1 \<or>p p2)[ss] = p1[ss] \<or>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_ImpliesP_distr [urename]:
"(p1 \<Rightarrow>p p2)[ss] = p1[ss] \<Rightarrow>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_IffP_distr [urename]:
"(p1 \<Leftrightarrow>p p2)[ss] = p1[ss] \<Leftrightarrow>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_ExistsP_distr1 [urename]:
"(\<exists>p vs . p)[ss] = (\<exists>p ss `\<^sub>s vs . p[ss])"
apply (utp_pred_tac)
apply (safe)
apply (rule_tac x="RenameB ss b'" in exI)
apply (simp add:RenameB_override_distr1 closure)
apply (rule_tac x="RenameB (inv\<^sub>s ss) b'" in exI)
apply (simp add:RenameB_override_distr1 closure)
done

theorem RenameP_ExistsP_distr2 [urename]:
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<exists>p vs2 . p)[ss] = (\<exists>p vs2 . p[ss])"
  apply (simp add:RenameP_ExistsP_distr1)
  apply (metis VAR_RENAME_ON_disj_image rename_image_def)
done

theorem RenameP_ForallP_distr [urename]:
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<forall>p vs2 . p)[ss] = (\<forall>p vs2 . p[ss])"
apply (simp add: ForallP_def closure)
apply (simp add: RenameP_ExistsP_distr2 RenameP_NotP_distr closure)
done

theorem RenameP_ClosureP [urename]:
"[p[ss]]p = [p]p"
apply (utp_pred_tac)
apply (safe)
apply (drule_tac x = "RenameB ss x" in spec)
apply (simp_all)
done

theorem RenameP_VarP [urename]:
"(VarP x)[ss] = VarP (\<langle>ss\<rangle>\<^sub>s x)"
  apply (utp_pred_tac)
  apply (simp add:RenameB_def)
done

theorem RenameP_EqualP [urename]:
"(e ==p f)[ss] = e[ss]\<epsilon> ==p f[ss]\<epsilon>"
  apply (utp_pred_tac)
  apply (utp_expr_tac)
done

theorem RenameE_VarE [urename]:
"(VarE x)[ss]\<epsilon> = VarE (\<langle>ss\<rangle>\<^sub>s x)"
  apply (utp_expr_tac)
  apply (simp add:RenameB_def)
done

subsubsection {* Other renaming laws *}

theorem RenameP_UNREST [simp]:
"\<lbrakk> UNREST vs p; ss \<in> VAR_RENAME_ON vs \<rbrakk> \<Longrightarrow> p[ss] = p"
  apply (utp_pred_tac)
  apply (rule allI)
  apply (frule VAR_RENAME_ON_inv)
  apply (simp add:VAR_RENAME_ON_def)
  apply (simp add:RenameB_def EvalP_def UNREST_def)
  apply (rule iffI)
  apply (subgoal_tac "(CompB b ss) \<oplus>\<^sub>b b on vs = b")
  apply (drule_tac x="CompB b ss" in bspec, simp)
  apply (drule_tac x="b" in spec, simp)
  apply (force simp add:override_on_def) 
  apply (subgoal_tac "b \<oplus>\<^sub>b (CompB b ss) on vs = CompB b ss")
  apply (drule_tac x="b" in bspec, simp)
  apply (drule_tac x="CompB b ss" in spec)
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
"taut [p1 \<Leftrightarrow>p p2]p \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]p"
apply (utp_pred_auto_tac)
oops

theorem SubstP_invariant_taut :
"taut [p1 \<Leftrightarrow>p p2]p \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]p"
apply (subgoal_tac "p1[ss] \<Leftrightarrow>p p2[ss] = (p1 \<Leftrightarrow>p p2)[ss]")
apply (simp)
apply (simp add: RenameP_ClosureP closure)
apply (utp_pred_tac)
apply (simp add: RenameP_IffP_distr)
done

theorem ExistsP_OrP_expand:
"(\<exists>p vs. p1 \<or>p p2) = (\<exists>p vs. p1) \<or>p (\<exists>p vs. p2)"
  by (utp_pred_auto_tac)

theorem ExistsP_AndP_expand1:
"\<lbrakk>UNREST vs p2\<rbrakk> \<Longrightarrow>
 (\<exists>p vs. p1) \<and>p p2 = (\<exists>p vs. (p1 \<and>p p2))"
  by (utp_pred_tac, metis EvalP_ExistsP EvalP_def ExistsP_ident UNREST_binding_override)

theorem ExistsP_AndP_expand2:
"\<lbrakk>UNREST vs p1\<rbrakk> \<Longrightarrow>
 p1 \<and>p (\<exists>p vs. p2) = (\<exists>p vs. (p1 \<and>p p2))"
  by (utp_pred_tac, metis EvalP_ExistsP EvalP_def ExistsP_ident UNREST_binding_override)

text {* Lifting of exists around sequential composition requires that p1 and p2 are relations 
        and that p1 does use any of the inputs hidden by vs as inputs *}
theorem ExistsP_SemiP_expand1:
  assumes unrests: "UNREST DASHED_TWICE p1" "UNREST DASHED_TWICE p2"
  and     noconn:"UNREST (dash ` in vs) p1"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  shows "p1 ; (\<exists>p vs. p2) = (\<exists>p out vs. (p1 ; p2))"
proof -

  from unrests have "UNREST DASHED_TWICE (\<exists>p vs . p2)"
    by (blast intro:unrest)

  with unrests
  have "p1 ; (\<exists>p vs. p2) = (\<exists>p DASHED_TWICE . p1[SS1] \<and>p (\<exists>p vs . p2)[SS2])"
    by (simp add:SemiR_algebraic)

  also have "... = (\<exists>p DASHED_TWICE . p1[SS1] \<and>p (\<exists>p (SS2 `\<^sub>s vs) . p2[SS2]))"
    by (simp add: RenameP_ExistsP_distr1)

  also have "... = (\<exists>p DASHED_TWICE . \<exists>p (SS2 `\<^sub>s vs) . (p1[SS1] \<and>p p2[SS2]))"
  proof -
    from unrests have "UNREST (SS2 `\<^sub>s vs) p1[SS1]"
    proof -

      have "dash ` (in vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:var_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:var_defs)

      moreover from assms have "UNREST (dash ` dash ` in vs) p1[SS1]"
        by (smt SS1_UNDASHED_DASHED_image UNREST_RenameP_alt Un_empty_left calculation(1) in_dash in_in le_iff_sup out_dash rename_image_def sup.idem)

      moreover from assms have "UNREST (out vs) p1[SS1]"
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

  also from assms have "... = (\<exists>p out vs. \<exists>p DASHED_TWICE . p1[SS1] \<and>p p2[SS2])"
  proof -
    have "DASHED_TWICE \<union> dash ` dash ` (in vs) = DASHED_TWICE"
      by (force simp add:var_defs)

    thus ?thesis using assms
      apply (simp add:SS2_simps)
      apply (smt ExistsP_union SS2_UNDASHED_DASHED_image rename_image_def sup_commute)
    done
  qed

  also from assms have "... = (\<exists>p out vs. (p1 ; p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

theorem ExistsP_SemiP_expand2:
  assumes unrests: "UNREST DASHED_TWICE p1" "UNREST DASHED_TWICE p2"
  and     "vs \<subseteq> UNDASHED \<union> DASHED"
  and     noconn:"UNREST (undash ` out vs) p2"
  shows "(\<exists>p vs. p1) ; p2 = (\<exists>p in vs. (p1 ; p2))"
proof -

  from unrests have "UNREST DASHED_TWICE (\<exists>p vs . p1)"
    by (blast intro:unrest)

  with unrests
  have "(\<exists>p vs. p1) ; p2 = (\<exists>p DASHED_TWICE . (\<exists>p vs . p1)[SS1] \<and>p p2[SS2])"
    by (simp add:SemiR_algebraic closure)

  also have "... = (\<exists>p DASHED_TWICE . (\<exists>p (SS1 `\<^sub>s vs) . p1[SS1]) \<and>p p2[SS2])"
    by (metis (lifting) RenameP_ExistsP_distr1)

  also have "... = (\<exists>p DASHED_TWICE . \<exists>p (SS1 `\<^sub>s vs) . (p1[SS1] \<and>p p2[SS2]))"
  proof -
    from unrests have "UNREST (SS1 `\<^sub>s vs) p2[SS2]"
    proof -

      have "undash ` (out vs) \<subseteq> UNDASHED \<union> DASHED"
        by (force simp add:var_defs)

      moreover have "dash ` out vs \<subseteq> DASHED_TWICE"
        by (force simp add:var_defs)

      moreover from assms have "UNREST (dash ` out vs) p2[SS2]"
        apply (rule_tac ?vs1.0="undash ` out vs" in UNREST_RenameP_alt)
        apply (auto simp add:var_member closure calculation var_simps SS2_simps)
        apply (smt SS2.rep_eq dash_UNDASHED_image image_iff in_mono undash_dash utp_var.out_DASHED)
      done

      moreover from assms have "UNREST (in vs) p2[SS2]"
        apply (rule_tac ?vs1.0="dash ` dash ` in vs" in UNREST_RenameP_alt)
        apply (force intro:  UNREST_subset simp add:var_defs)
        apply (auto simp add:closure alphabet_defs image_def)
        apply (rule_tac x="dash (dash x)" in exI)
        apply (auto simp add:SS2_simps SS2.rep_eq)
        apply (metis (lifting) DASHED_dash_DASHED_TWICE UNDASHED_dash_DASHED set_mp utp_var.in_UNDASHED)
      done

      ultimately show ?thesis using assms
        by (metis (lifting) SS1_UNDASHED_DASHED_image UNREST_union)
    qed

    thus ?thesis
      by (metis (lifting) ExistsP_AndP_expand1)
  qed

  also from assms have "... = (\<exists>p in vs. \<exists>p DASHED_TWICE . p1[SS1] \<and>p p2[SS2])"
  proof -
    have "dash ` (out vs) \<union> DASHED_TWICE = DASHED_TWICE"
      by (force simp add:var_defs)

    thus ?thesis using assms
      apply (simp add:SS1_simps)
      apply (smt ExistsP_union SS1_UNDASHED_DASHED_image Un_commute rename_image_def)
    done
  qed

  also from assms have "... = (\<exists>p in vs. (p1 ; p2))"
    by (simp add:SemiR_algebraic closure)

  ultimately show ?thesis
    by simp
qed

(* Note that assumption assumption 2 is automatic under a homogeneous alphabet.
    The following proof is performed by application of existential lifting.
 *)

theorem SemiP_SkipRA_right :
  assumes 
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
    by (auto simp add:var_simps var_defs)

  moreover from assms have "out (UNDASHED \<union> DASHED - vs) = DASHED - out vs "
    by (auto simp add:var_simps var_defs)

  moreover have "(UNDASHED \<union> DASHED) - vs \<subseteq> (UNDASHED \<union> DASHED)"
    by force

  moreover from assms have "p ; II = p"
    by (utp_rel_auto_tac)

  ultimately show ?thesis using assms
    by (metis (lifting) ExistsP_SemiP_expand1 ExistsP_ident SkipRA.rep_eq)
qed

theorem SemiP_SkipRA_left :
  assumes 
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
    by (auto simp add:var_simps var_defs)

  moreover from assms have "in (UNDASHED \<union> DASHED - vs) = UNDASHED - in vs "
    by (auto simp add:var_simps var_defs)

  moreover from assms have "II ; p = p"
    by (utp_rel_auto_tac)

  ultimately show ?thesis using assms
    by (metis (lifting) ExistsP_SemiP_expand2 ExistsP_ident SkipRA.rep_eq)
qed

theorem SkipRA_empty :
  shows "II {} = true"
  apply (simp add:SkipRA_def)
  apply (utp_pred_tac)
  apply (rule_tac x="\<B>" in exI)
  apply (simp add:default_binding.rep_eq)
done

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

theorem SkipRA_assign :
  assumes "x \<in> vs" "dash x \<in> vs" "x \<in> UNDASHED" "HOMOGENEOUS vs"
  shows "II vs = x :=p\<^bsub>vs\<^esub> VarE x"
  by (simp add:AssignR_def SkipRA_unfold assms)

theorem SemiP_ExistsP_left:
  assumes
  "UNREST DASHED_TWICE p" "UNREST DASHED_TWICE q"
  "UNREST (DASHED - vs1) p" "UNREST (UNDASHED - vs2) q"
  "vs1 \<subseteq> DASHED" "vs2 \<subseteq> UNDASHED"
  "dash ` vs2 \<subseteq> vs1"
  shows "(\<exists>p (vs1 - dash ` vs2). p) ; q = p ; q"
proof -

  let ?A = "dash ` out vs1 - dash ` dash ` in vs2"

  from assms have UNREST: "UNREST DASHED_TWICE (\<exists>p vs1 - dash ` vs2 . p)"
    by (auto intro:unrest)

  hence "(\<exists>p (vs1 - dash ` vs2). p) ; q = 
        (\<exists>p DASHED_TWICE .
         (\<exists>p ?A . p[SS1]) \<and>p q[SS2])"
  proof -

    from assms have "vs1 \<subseteq> UNDASHED \<union> DASHED"
      by (auto)

    with UNREST show ?thesis using assms
      apply (simp add: SemiR_algebraic closure urename var_simps)
      apply (simp add: SS1_UNDASHED_DASHED_image[simplified] var_simps var_dist closure)
    done
  qed

  also from assms(4) have "... = (\<exists>p DASHED_TWICE . (\<exists>p ?A . p[SS1] \<and>p q[SS2]))"
  proof -
    from assms(4) have "UNREST ?A q[SS2]"
      apply (rule unrest)
      apply (subgoal_tac "UNDASHED - vs2 \<subseteq> UNDASHED \<union> DASHED")
      apply (simp add: SS2_UNDASHED_DASHED_image[simplified] var_simps var_dist closure)
      apply (auto intro: unrest)
      apply (metis (lifting) DASHED_dash_DASHED_TWICE set_rev_mp utp_var.out_DASHED)
    done

    thus ?thesis
      by (metis ExistsP_AndP_expand1)
  qed

  also have "... = (\<exists>p DASHED_TWICE . p[SS1] \<and>p q[SS2])"
  proof -
    have "?A \<subseteq> DASHED_TWICE"
      by (auto simp add:var_defs)

    thus ?thesis
      by (metis ExistsP_union sup_absorb1)
  qed

  ultimately show ?thesis using assms UNREST
    by (simp add:SemiR_algebraic)
qed
    
theorem SemiP_ExistsP_right:
  assumes
  "UNREST DASHED_TWICE p" "UNREST DASHED_TWICE q"
  "UNREST (DASHED - vs1) p" "UNREST (UNDASHED - vs2) q"
  "vs1 \<subseteq> DASHED" "vs2 \<subseteq> UNDASHED"
  "vs1 \<subseteq> dash ` vs2"
  shows "p ; (\<exists>p (vs2 - undash ` vs1). q) = p ; q"
proof -

  let ?A = "dash ` dash ` in vs2 - (dash ` dash ` in (undash ` vs1) \<union> out (undash ` vs1))"

  from assms have UNREST: "UNREST DASHED_TWICE (\<exists>p vs2 - undash ` vs1 . q)"
    by (auto intro:unrest)

  hence "p ; (\<exists>p (vs2 - undash ` vs1). q) = 
        (\<exists>p DASHED_TWICE .
         p[SS1] \<and>p (\<exists>p ?A . q[SS2]))"
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

  also have "... = (\<exists>p DASHED_TWICE . (\<exists>p ?A . p[SS1] \<and>p q[SS2]))"
  proof -
    from assms(3) have "UNREST ?A p[SS1]"
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

  also have "... = (\<exists>p DASHED_TWICE . p[SS1] \<and>p q[SS2])"
  proof -
    have "?A \<subseteq> DASHED_TWICE"
      by (auto simp add:var_defs)

    thus ?thesis
      by (smt ExistsP_union sup_absorb1)
  qed

  ultimately show ?thesis using assms UNREST
    by (simp add:SemiR_algebraic)
qed

theorem SemiR_OrR_distl :
"r1 ; (r2 \<or>p r3) = (r1 ; r2) \<or>p (r1 ; r3)"
  by utp_rel_tac

theorem SemiR_OrR_distr :
"(r1 \<or>p r2) ; r3 = (r1 ; r3) \<or>p (r2 ; r3)"
  by utp_rel_tac

theorem SemiR_CondR_distr:
  assumes 
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
    by (metis ExistsP_ident SS1_VAR_RENAME_ON RenameP_UNREST UNREST_ExistsP)

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

text {* Expressions renaming *}

theorem RenameE_id :
"p[id\<^sub>s]\<epsilon> = p"
  by (utp_expr_tac)

theorem RenameE_inverse1 :
"e[ss]\<epsilon>[inv\<^sub>s ss]\<epsilon> = e"
  by (utp_expr_tac)

theorem RenameE_inverse2 :
"e[inv\<^sub>s ss]\<epsilon>[ss]\<epsilon> = e"
  by (utp_expr_tac)

theorem RenameE_compose :
"e[ss1]\<epsilon>[ss2]\<epsilon> = e[ss2 \<circ>\<^sub>s ss1]\<epsilon>"
apply (utp_expr_tac)
apply (simp add: RenameB_compose closure)
done

theorem RenameE_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (e::'VALUE WF_EXPRESSION)[ss1]\<epsilon>[ss2]\<epsilon> = e[ss2]\<epsilon>[ss1]\<epsilon>"
apply (utp_expr_tac)
apply (clarify)
apply (subst RenameB_commute [of "(inv\<^sub>s ss1)" "vs1" "(inv\<^sub>s ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

theorem RenameE_involution [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_INV\<rbrakk> \<Longrightarrow>
 p[ss]\<epsilon>[ss]\<epsilon> = p"
  by (utp_expr_tac)

theorems erename_simps =
  RenameE_id
  RenameE_inverse1
  RenameE_inverse2
  RenameE_compose
  RenameE_involution

text {* Expression substitution *}

theorem SubstP_no_var:
  "\<lbrakk> e \<rhd>\<^sub>e x; \<exists> z. is_SubstP_var p e x z; UNREST_EXPR {x} e; UNREST {x} p \<rbrakk> \<Longrightarrow>
  p[e|x] = p"
  apply (unfold SubstP_one_point[THEN sym])
  apply (unfold ExistsP_AndP_expand2[THEN sym])
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (auto)
  apply (metis EvalE_UNREST_assign EvalE_compat binding_upd_apply insertI1)
done

lemma is_SubstP_var_equiv:
  "\<lbrakk> is_SubstP_var p v x x'; 
     is_SubstP_var p v x x''; v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> 
     SubstP_body p v x x' = SubstP_body p v x x''" 
  apply (subgoal_tac "v \<rhd>\<^sub>e x'")
  apply (subgoal_tac "v \<rhd>\<^sub>e x''")
  apply (simp add:SubstP_def SubstP_body_def is_SubstP_var_def)
  apply (erule conjE)+
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (clarify)
  apply (simp add:binding_upd_twist)
  apply (rule iffI)
  apply (rule_tac x="b(x'' :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b)" in exI)
  apply (erule exE, erule conjE)
  apply (simp add:binding_upd_twist)
  apply (metis EvalP_ExistsP_singleton EvalP_ForallP_singleton ExistsP_ident ForallP_ident binding_value_alt)
  apply (rule_tac x="b(x' :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b)" in exI)
  apply (erule exE, erule conjE)
  apply (simp add:binding_upd_twist)
  apply (metis EvalP_ExistsP_singleton EvalP_ForallP_singleton ExistsP_ident ForallP_ident binding_value_alt)
  apply (simp add:evar_compat_def is_SubstP_var_def var_compat_def)
  apply (simp add:evar_compat_def is_SubstP_var_def var_compat_def)
done

lemma is_SubstP_var_UNDASHED: 
  "\<lbrakk> x \<in> UNDASHED; 
     UNREST {dash (dash x)} p; 
     UNREST_EXPR {dash (dash x)} v \<rbrakk> \<Longrightarrow> 
   is_SubstP_var p v x (dash (dash x))"
  by (simp add:is_SubstP_var_def)

lemma is_SubstP_var_DASHED: 
  "\<lbrakk> x \<in> DASHED; 
     UNREST {dash x} p; 
     UNREST_EXPR {dash x} v \<rbrakk> \<Longrightarrow> 
   is_SubstP_var p v x (dash x)"
  by (simp add:is_SubstP_var_def)

lemma SubstP_UNDASHED:
  assumes 
    "x \<in> UNDASHED" "UNREST {dash (dash x)} p"
    "UNREST_EXPR {dash (dash x)} v" "v \<rhd>\<^sub>e x"
  shows "p[v|x] = (\<exists>p {dash (dash x)} . p\<^bsup>[x \<mapsto> dash (dash x)]\<^esup> \<and>p (VarE (dash (dash x)) ==p v))"
proof -

  from assms have "p[v|x] = SubstP_body p v x (SOME x'. is_SubstP_var p v x x')"
    by (simp add:SubstP_def)

  also from assms have "... = SubstP_body p v x (dash (dash x))"
  proof -
    from assms have "is_SubstP_var p v x (dash (dash x))"
      by (simp add: is_SubstP_var_UNDASHED)

    thus ?thesis using assms
      apply (rule_tac is_SubstP_var_equiv)
      apply (rule someI)
      apply (simp_all)
    done
  qed

  ultimately show ?thesis
    by (simp add:SubstP_body_def)
qed

lemma SubstP_DASHED:
  assumes 
    "x \<in> DASHED" "UNREST {dash x} p"
    "UNREST_EXPR {dash x} v" "v \<rhd>\<^sub>e x"
  shows "p[v|x] = (\<exists>p {dash x} . p\<^bsup>[x \<mapsto> dash x]\<^esup> \<and>p (VarE (dash x) ==p v))"
proof -

  from assms have "p[v|x] = SubstP_body p v x (SOME x'. is_SubstP_var p v x x')"
    by (simp add:SubstP_def)

  also from assms have "... = SubstP_body p v x (dash x)"
  proof -
    from assms have "is_SubstP_var p v x (dash x)"
      by (simp add: is_SubstP_var_DASHED)

    thus ?thesis using assms
      apply (rule_tac is_SubstP_var_equiv)
      apply (rule someI)
      apply (simp_all)
    done
  qed

  ultimately show ?thesis
    by (simp add:SubstP_body_def)
qed

lemma 
  assumes 
    "UNREST DASHED_TWICE p"
    "UNREST_EXPR (VAR - vs) v"  
    "x \<in> UNDASHED"
    "vs \<subseteq> UNDASHED"
    "v \<rhd>\<^sub>e x"
  shows "x :=p\<^bsub>vs\<^esub> v ; p = p[v|x]"
  oops

lemma utp_pred_simps [simp]:
  "\<not>p false = true"
  "\<not>p true  = false"
  "false \<and>p x = false" 
  "x \<and>p false = false"
  "true \<and>p x = x"
  "x \<and>p true = x"
  "false \<Rightarrow>p x = true" 
  "true \<Rightarrow>p x = x" 
  "p \<Rightarrow>p true = true" 
  "p \<Rightarrow>p false = \<not>p p"
  by (utp_pred_tac)+

subsubsection {* Additional EvalP laws *}

lemma EvalP_UNREST_binding_override [eval]:
  "\<lbrakk> UNREST vs p \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>p\<rbrakk>b1"
  by (metis EvalP_ExistsP EvalP_ForallP ExistsP_ident ForallP_ident)

lemma EvalP_UNREST_binding_upd [eval]:
  "\<lbrakk> UNREST vs p; x \<in> vs; v \<rhd> x \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)) = \<lbrakk>p\<rbrakk>b"
  apply (auto simp add:UNREST_def EvalP_def)
  apply (drule_tac x="b(x :=\<^sub>b v)" in bspec, simp)
  apply (drule_tac x="b" in spec)
  apply (simp)
  apply (drule_tac x="b" in bspec, simp)
  apply (drule_tac x="b(x :=\<^sub>b v)" in spec)
  apply (simp add:override_on_def binding_equiv_def)
done

end