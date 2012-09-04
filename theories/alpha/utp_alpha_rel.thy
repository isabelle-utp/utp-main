(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_rel.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Predicates *}

theory utp_alpha_rel
imports "../core/utp_pred" "../core/utp_laws" utp_alpha_pred "../tactics/utp_alpha_tac" "../tactics/utp_rel_tac"
begin

context ALPHA_PRED
begin

subsection {* Restrictions *}

definition WF_RELATION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_RELATION =
 {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p \<subseteq> UNDASHED \<union> DASHED}"

definition WF_HOM_ALPHABET :: "'TYPE ALPHABET set" where
"WF_HOM_ALPHABET = {a. a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<union> DASHED \<and> dash ` in a = out a}"

subsection {* Operators *}

subsubsection {* Sequence *}

definition SkipA :: "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"SkipA a = (a, \<exists>p (VAR - a). SkipR)"

notation SkipA ("II\<alpha>")

definition SemiA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<longrightarrow>
 SemiA r1 r2 = (in (\<alpha> r1) \<union> out (\<alpha> r2), \<pi> r1 ; \<pi> r2)"

notation SemiA (infixr ";\<alpha>" 140)

subsection {* Theorems *}

theorem WF_ALPHA_RELATION_WF_ALPHABET [closure] :
"r \<in> WF_RELATION \<Longrightarrow> \<alpha> r \<in> WF_ALPHABET"
  by (simp add: WF_RELATION_def closure)

theorem WF_ALPHA_PREDICATE_WF_PREDICATE [closure] :
"r \<in> WF_RELATION \<Longrightarrow> r \<in> WF_ALPHA_PREDICATE"
  by (simp add: WF_RELATION_def)

theorem WF_ALPHA_PREDICATE_UNDASHED_DASHED [closure] :
"r \<in> WF_RELATION \<Longrightarrow> \<alpha> r \<subseteq> UNDASHED \<union> DASHED"
  by (simp add:WF_RELATION_def)

subsubsection {* Closure Theorems *}

theorem AndA_rel_closure[closure]:
"\<lbrakk> r1 \<in> WF_RELATION; r2 \<in> WF_RELATION \<rbrakk> \<Longrightarrow> r1 \<and>\<alpha> r2 \<in> WF_RELATION"
  apply (simp add:WF_RELATION_def)
  apply (simp add:closure alphabet)
done

theorem OrA_rel_closure[closure]:
"\<lbrakk> r1 \<in> WF_RELATION; r2 \<in> WF_RELATION \<rbrakk> \<Longrightarrow> r1 \<or>\<alpha> r2 \<in> WF_RELATION"
  apply (simp add:WF_RELATION_def)
  apply (simp add:closure alphabet)
done

theorem SkipA_closure[closure]: 
"a \<in> WF_HOM_ALPHABET \<Longrightarrow> II\<alpha> a \<in> WF_RELATION"
  apply (simp add:WF_HOM_ALPHABET_def SkipA_def WF_RELATION_def WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (simp add:closure)
  apply (insert UNREST_ExistsP [of "II" "{}" "VAR - a"])
  apply (simp add:closure UNREST_empty)
done

theorem SemiA_closure[closure]: 
  assumes "r1 \<in> WF_RELATION" "r2 \<in> WF_RELATION"
  shows "r1 ;\<alpha> r2 \<in> WF_RELATION"
proof -
  from assms have "in (\<alpha> r1) \<union> out (\<alpha> r2) \<in> WF_ALPHABET"
    by (simp add:closure)

  moreover with assms have "\<pi> r1 ; \<pi> r2 \<in> WF_PREDICATE_OVER (in (\<alpha> r1) \<union> out (\<alpha> r2))"
  proof -

    from assms have "UNREST (VAR - \<alpha> r1) (\<pi> r1)"
      by (simp add:closure)

    moreover with assms have "UNREST DASHED_TWICE (\<pi> r1)"
      apply (rule_tac UNREST_subset)
      apply (auto)
      apply (subgoal_tac "\<alpha> r1 \<subseteq> UNDASHED \<union> DASHED")
      apply (metis DASHED_DASHED_TWICE_contra UNDASHED_DASHED_TWICE_contra Un_iff set_mp)
      apply (simp_all add:closure)
    done

    moreover from assms have "UNREST (VAR - \<alpha> r2) (\<pi> r2)"
      by (simp add:closure)

    moreover with assms have "UNREST DASHED_TWICE (\<pi> r2)"
      apply (rule_tac UNREST_subset)
      apply (auto)
      apply (subgoal_tac "\<alpha> r2 \<subseteq> UNDASHED \<union> DASHED")
      apply (metis DASHED_not_DASHED_TWICE UNDASHED_DASHED_TWICE_contra UnE in_mono)
      apply (simp_all add:closure)
    done

    moreover     
    from assms have "(VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2)) 
                     \<subseteq> VAR - (in (\<alpha> r1) \<union> dash ` out (\<alpha> r1))"
      by (auto simp add:out_alphabet_def)

    moreover     
    from assms have "(VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2)) 
                     \<subseteq> VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))"
      by (auto simp add:in_alphabet_def)

    moreover
    with assms have "UNREST (SS1 ` (VAR - \<alpha> r1)) (\<pi> r1[SS1])"
      apply (rule_tac UNREST_SubstP)
      apply (simp_all add:closure)
    done

    moreover
    with assms have "UNREST (SS1 ` VAR - SS1 ` (\<alpha> r1)) (\<pi> r1[SS1])"
      apply (subgoal_tac "inj SS1")
      apply (metis image_set_diff)
      apply (metis SS1_VAR_SUBST SS1_inv VAR_SUBST_inv_ss_app inj_on_def)
    done
      
    moreover
    with assms have "UNREST (VAR - (in (\<alpha> r1) \<union> dash ` out (\<alpha> r1))) (\<pi> r1[SS1])"
      apply (simp add:closure SS1_image)
      apply (subgoal_tac "surj SS1")
      apply (simp add:VAR_def)
      apply (insert SS1_VAR_SUBST)
      apply (simp add:VAR_SUBST_def bij_def)
    done

    moreover 
    with calculation assms have "UNREST ((VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))) (\<pi> r1[SS1])"
      apply (rule_tac ?vs1.0="VAR - (in (\<alpha> r1) \<union> dash ` out (\<alpha> r1))" in UNREST_subset)
      apply (auto simp add:closure)
    done

    moreover
    with assms have "UNREST (SS2 ` (VAR - \<alpha> r2)) (\<pi> r2[SS2])"
      apply (rule_tac UNREST_SubstP)
      apply (simp_all add:closure)
    done

    moreover
    from assms have "SS2 ` (VAR - \<alpha> r2) = VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))"
    proof -
      have "SS2 ` (VAR - \<alpha> r2) = SS2 ` VAR - SS2 ` (\<alpha> r2)"
        by (metis image_set_diff SS2_VAR_SUBST VAR_SUBST_bij bij_betw_imp_inj_on)

      also from assms have "... = VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))"
        apply (simp add:closure SS2_image VAR_def)
        apply (insert SS2_VAR_SUBST)
        apply (simp add:VAR_SUBST_def bij_def)
      done

      ultimately show ?thesis by simp
    qed

    moreover
    with calculation assms have "UNREST ((VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))) (\<pi> r2[SS2])"
      apply (rule_tac ?vs1.0="VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))" in UNREST_subset)
      apply (auto simp add:closure)
    done

    moreover from assms calculation have "UNREST (((VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))) \<union> DASHED_TWICE) (\<exists>p DASHED_TWICE . ((\<pi> r1[SS1]) \<and>p (\<pi> r2[SS2])))"
      apply (rule_tac UNREST_ExistsP)
      apply (simp add:closure)
      apply (rule_tac UNREST_AndP)
      apply (simp_all add:closure)
    done

    ultimately show ?thesis using assms
      apply (simp add:WF_PREDICATE_OVER_def closure)
      apply (subgoal_tac "UNREST DASHED_TWICE (\<pi> r1)")
      apply (subgoal_tac "UNREST DASHED_TWICE (\<pi> r2)")
      apply (simp add:SemiR_algebraic closure)
      apply (subgoal_tac "VAR - DASHED_TWICE - (in (\<alpha> r1) \<union> out (\<alpha> r2)) \<union> DASHED_TWICE =
                          VAR - (in (\<alpha> r1) \<union> out (\<alpha> r2))") 
      apply (force)
      apply (subgoal_tac "(in (\<alpha> r1) \<union> out (\<alpha> r2)) \<inter> DASHED_TWICE = {}")
      apply (force)
      apply (safe)
      apply (simp add:alphabet_defs)
      apply (simp add:alphabet_defs)
    done
  qed

  ultimately show ?thesis using assms
    by (auto simp add:SemiA_def WF_RELATION_def WF_ALPHA_PREDICATE_def alphabet_defs)

qed

subsubsection {* Laws *}

theorem SemiA_assoc: 
  assumes "r1 \<in> WF_RELATION" "r2 \<in> WF_RELATION" "r3 \<in> WF_RELATION"
  shows "(r1 ;\<alpha> r2) ;\<alpha> r3 = r1 ;\<alpha> (r2 ;\<alpha> r3)"
  apply (subgoal_tac "r1 ;\<alpha> r2 \<in> WF_RELATION", subgoal_tac "r2 ;\<alpha> r3 \<in> WF_RELATION")
  apply (insert assms, simp add:closure SemiA_def SemiP_assoc alphabet)
  apply (simp_all add:closure)
done

theorem SemiA_OrA_distr :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 ;\<alpha> (r2 \<or>\<alpha> r3) = (r1 ;\<alpha> r2) \<or>\<alpha> (r1 ;\<alpha> r3)"
  apply (subgoal_tac "(r1 ;\<alpha> r2) \<in> WF_RELATION")
  apply (subgoal_tac "(r1 ;\<alpha> r3) \<in> WF_RELATION")
  apply (subgoal_tac "(r2 \<or>\<alpha> r3) \<in> WF_RELATION")
  apply (simp add:OrA_def SemiA_def closure alphabet)
  apply (rule conjI)
  apply (force)
  apply (rule SemiP_OrP_distr)
  apply (simp_all add:closure)
done
 
theorem SemiP_SkipR_left :
"\<lbrakk>r \<in> WF_RELATION; a \<in> WF_HOM_ALPHABET; out a = dash ` in (\<alpha> r) \<rbrakk> \<Longrightarrow>
 II\<alpha> a ;\<alpha> r = r"
  apply(simp add:SemiA_def closure)
  apply(simp add:SkipA_def closure)
  apply(simp add:WF_HOM_ALPHABET_def)
  oops 

end

end