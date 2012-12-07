(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_rel.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Predicates *}

theory utp_alpha_rel
imports utp_alpha_pred utp_alpha_expr
  "../tactics/utp_alpha_tac" "../tactics/utp_rel_tac"
begin

context ALPHA_PRED
begin

subsection {* Restrictions *}

definition REL_ALPHABET :: "'TYPE ALPHABET set" where
"REL_ALPHABET = {a . a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<union> DASHED}"

definition HOM_ALPHABET :: "'TYPE ALPHABET set" where
"HOM_ALPHABET = {a . a \<in> REL_ALPHABET \<and> HOMOGENEOUS a}"

definition WF_RELATION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_RELATION = {p . p \<in> WF_ALPHA_PREDICATE \<and> (\<alpha> p) \<in> REL_ALPHABET}"

definition WF_CONDITION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_CONDITION = {p . p \<in> WF_RELATION \<and> UNREST DASHED (\<pi> p)}"

subsection {* Operators *}

subsubsection {* Skip *}

definition SkipA :: "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> REL_ALPHABET \<longrightarrow>
 SkipA a = (a, SkipRA a)"

notation SkipA ("II\<alpha>")

subsubsection {* Assignment *}

definition AssignA ::
"'TYPE VAR \<Rightarrow>
 'TYPE ALPHABET \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> REL_ALPHABET \<Longrightarrow>
 AssignA x a v \<equiv> (a, AssignR x a (\<epsilon> v))"

notation AssignA ("_ :=\<^bsub>_ \<^esub>_" [190] 190)

subsubsection {* Conditional *}

text {* Should we impose a constraint on b for it to be a condition? *}

definition CondA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<and>
 b \<in> WF_CONDITION \<and>
 (\<alpha> r1) = (\<alpha> r2) \<and>
 (\<alpha> b) \<subseteq> (\<alpha> r1) \<longrightarrow>
 CondA r1 b r2 = (\<alpha> r1, (\<pi> r1) \<triangleleft> (\<pi> b) \<triangleright> (\<pi> r2))"

notation CondA ("_ \<triangleleft>\<alpha> _ \<alpha>\<triangleright> _")

subsubsection {* Sequential Composition *}

definition SemiA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<longrightarrow>
 SemiA r1 r2 = (in (\<alpha> r1) \<union> out (\<alpha> r2), (\<pi> r1) ; (\<pi> r2))"

notation SemiA (infixr ";\<alpha>" 140)

subsection {* Theorems *}

theorem WF_RELATION_unfold :
"r \<in> WF_RELATION \<longleftrightarrow>
 r \<in> WF_ALPHA_PREDICATE \<and>
 (\<alpha> r) \<subseteq> UNDASHED \<union> DASHED"
apply (simp add: WF_RELATION_def)
apply (simp add: REL_ALPHABET_def)
apply (safe)
apply (simp add: closure)
done

theorem WF_RELATION_intro [intro] :
  assumes "r \<in> WF_ALPHA_PREDICATE" "\<alpha> r \<subseteq> UNDASHED \<union> DASHED"
  shows "r \<in> WF_RELATION"
  by (simp add:WF_RELATION_unfold assms)

theorem WF_RELATION_WF_ALPHA_PREDICATE [closure] :
"r \<in> WF_RELATION \<Longrightarrow> r \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_RELATION_def)
done

theorem WF_CONDITION_WF_RELATION [closure] :
"r \<in> WF_CONDITION \<Longrightarrow> r \<in> WF_RELATION"
apply (simp add: WF_CONDITION_def)
done


theorem REL_ALPHABET_WF_ALPHABET [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow> a \<in> WF_ALPHABET"
apply (simp add: REL_ALPHABET_def)
done

theorem HOM_ALPHABET_REL_ALPHABET [closure] :
"a \<in> HOM_ALPHABET \<Longrightarrow> a \<in> REL_ALPHABET"
apply (simp add: HOM_ALPHABET_def)
done

theorem WF_RELATION_REL_ALPHABET [closure] :
"r \<in> WF_RELATION \<Longrightarrow> (\<alpha> r) \<in> REL_ALPHABET"
  by (simp add: WF_RELATION_def)

theorem WF_RELATION_UNDASHED_DASHED [closure]:
"r \<in> WF_RELATION \<Longrightarrow> (\<alpha> r) \<subseteq> UNDASHED \<union> DASHED"
apply (simp add: WF_RELATION_def)
apply (simp add: REL_ALPHABET_def)
done

subsubsection {* Closure Theorems *}

text {* TODO: Provide a complete set of closure theorems! *}

theorem NotA_WF_RELATION [closure] :
"\<lbrakk>r \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 \<not>\<alpha> r \<in> WF_RELATION"
apply (simp add: WF_RELATION_unfold)
apply (rule conjI)
apply (simp add: closure)
apply (simp_all add: alphabet)
done

theorem NotA_WF_CONDITION [closure] :
"\<lbrakk>r \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 \<not>\<alpha> r \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:closure)
apply (simp add:NotA_def closure)
apply (rule unrest)
apply (simp_all add:closure)
done

theorem AndA_WF_RELATION [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 \<and>\<alpha> r2 \<in> WF_RELATION"
apply (simp add: WF_RELATION_unfold)
apply (rule conjI)
apply (simp add: closure)
apply (simp_all add: alphabet)
done

theorem AndA_WF_CONDITION [closure] :
"\<lbrakk>r1 \<in> WF_CONDITION;
 r2 \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 r1 \<and>\<alpha> r2 \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:closure)
apply (simp add:AndA_def closure)
apply (rule unrest)
apply (simp_all add:closure)
done

theorem OrA_WF_RELATION [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 \<or>\<alpha> r2 \<in> WF_RELATION"
apply (simp add: WF_RELATION_unfold)
apply (rule conjI)
apply (simp add: closure)
apply (simp add: alphabet)
done

theorem OrA_WF_CONDITION [closure] :
"\<lbrakk>r1 \<in> WF_CONDITION;
 r2 \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 r1 \<or>\<alpha> r2 \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:closure)
apply (simp add:OrA_def closure)
apply (rule unrest)
apply (simp_all add:closure)
done

theorem ImpliesA_WF_RELATION [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 \<Rightarrow>\<alpha> r2 \<in> WF_RELATION"
apply (simp add:WF_RELATION_unfold)
apply (simp add: closure alphabet)
done

theorem ImpliesA_WF_CONDITION [closure] :
"\<lbrakk>r1 \<in> WF_CONDITION;
 r2 \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 r1 \<Rightarrow>\<alpha> r2 \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:closure)
apply (simp add:ImpliesA_def closure)
apply (rule unrest)
apply (simp_all add:closure)
done

theorem TrueA_WF_RELATION [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 true a \<in> WF_RELATION"
apply (simp add:WF_RELATION_def)
apply (simp add:closure alphabet)
done

theorem TrueA_WF_CONDITION [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 true a \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:closure)
apply (simp add:TrueA_def closure)
apply (rule unrest)
done

theorem FalseA_WF_RELATION [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 false a \<in> WF_RELATION"
apply (simp add:WF_RELATION_def)
apply (simp add:closure alphabet)
done

theorem FalseA_WF_CONDITION [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 false a \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:closure)
apply (simp add:FalseA_def closure)
apply (rule unrest)
done

theorem SkipA_closure [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 II\<alpha> a \<in> WF_RELATION"
apply (simp add: SkipA_def)
apply (simp add: WF_RELATION_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (simp add: REL_ALPHABET_def)
apply (clarify)
apply (auto intro: unrest closure)
done

theorem AssignA_closure [closure] :
  assumes 
   "a \<in> REL_ALPHABET"
   "x \<in> a" "dash x \<in> a"
   "x \<in> UNDASHED"
   "v \<in> WF_ALPHA_EXPRESSION"
   "\<alpha>\<epsilon> v \<subseteq> a"
  shows "x :=\<^bsub>a\<^esub> v \<in> WF_RELATION"
proof
  show "x :=\<^bsub>a \<^esub>v \<in> WF_ALPHA_PREDICATE"
  proof

    show "\<alpha> (x :=\<^bsub>a \<^esub>v) \<in> WF_ALPHABET" and "\<pi> (x :=\<^bsub>a \<^esub>v) \<in> WF_PREDICATE"
      by (simp_all add:AssignA_def assms closure)

    show "UNREST (VAR - \<alpha> (x :=\<^bsub>a \<^esub>v)) (\<pi> (x :=\<^bsub>a \<^esub>v))"
    proof (simp add:AssignA_def assms)
      have "UNREST (VAR - ({dash x} \<union> a)) (x :=p\<^bsub>a \<^esub>\<epsilon> v)"
        apply (rule UNREST_AssignR)
        apply (simp_all add:assms closure unrest)
        apply (rule_tac ?vs1.0="VAR - \<alpha>\<epsilon> v" in UNREST_EXPR_subset)
        apply (simp_all add: closure assms)
        apply (insert assms, force)
      done

      with assms show "UNREST (VAR - a) (x :=p\<^bsub>a \<^esub>\<epsilon> v)"
        by (metis insert_absorb insert_is_Un)
    qed
  qed

next
  
  from assms show "\<alpha> (x :=\<^bsub>a \<^esub>v) \<subseteq> UNDASHED \<union> DASHED"
    apply (simp add:AssignA_def closure)
    apply (simp add:REL_ALPHABET_def)
  done
qed

theorem CondA_closure [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 (\<alpha> r1) = (\<alpha> r2);
 (\<alpha> b) \<subseteq> (\<alpha> r1)\<rbrakk> \<Longrightarrow>
 (r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2) \<in> WF_RELATION"
apply (simp add: CondA_def)
apply (simp add: WF_RELATION_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (clarify)
apply (simp add: CondR_def closure)
apply (subgoal_tac "UNREST (VAR - \<alpha> r2) (\<pi> b)")
apply (auto intro!: UNREST_AndP UNREST_OrP UNREST_NotP) [1]
apply (auto simp: closure)
done

theorem SemiA_closure [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 ;\<alpha> r2 \<in> WF_RELATION"
apply (simp add: SemiA_def)
apply (simp add: WF_RELATION_unfold)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (clarify)
apply (subst SemiR_algebraic)
apply (simp_all add: closure)
-- {* Subgoal 1 *}
apply (subgoal_tac "DASHED_TWICE \<subseteq> VAR - \<alpha> r1")
apply (auto intro: UNREST_subset) [1]
apply (auto) [1]
-- {* Subgoal 2 *}
apply (subgoal_tac "DASHED_TWICE \<subseteq> VAR - \<alpha> r2")
apply (auto intro: UNREST_subset) [1]
apply (auto) [1]
-- {* Subgoal 3 *}
apply (rule conjI)
-- {* Subgoal 3.1 *}
oops

theorem SemiA_closure [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 ;\<alpha> r2 \<in> WF_RELATION"
apply (simp add: SemiA_def)
apply (simp add: WF_RELATION_unfold)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (clarify)
apply (simp add: SemiR_def)
apply (simp (no_asm_simp) add: UNREST_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "b1a \<oplus> b2 on (VAR - \<alpha> r1)" in exI)
apply (rule_tac x = "b2a \<oplus> b2 on (VAR - \<alpha> r2)" in exI)
apply (safe)
-- {* Subgoal 1.1 *}
-- {* Subgoal 1.2 *}
-- {* Subgoal 1.3 *}
-- {* Subgoal 1.4 *}
-- {* Subgoal 2 *}
-- {* Subgoal 3 *}
oops

theorem SemiA_closure [closure] :
  assumes
    "r1 \<in> WF_RELATION"
    "r2 \<in> WF_RELATION"
  shows "r1 ;\<alpha> r2 \<in> WF_RELATION"
proof -
  from assms have "in (\<alpha> r1) \<union> out (\<alpha> r2) \<in> WF_ALPHABET"
    by (simp add: closure)

  moreover with assms have "\<pi> r1 ; \<pi> r2 \<in> WF_PREDICATE_OVER (in (\<alpha> r1) \<union> out (\<alpha> r2))"
  proof -

    from assms have "UNREST (VAR - \<alpha> r1) (\<pi> r1)"
      by (simp add: closure)

    moreover with assms have "UNREST DASHED_TWICE (\<pi> r1)"
      apply (rule_tac UNREST_subset)
      apply (auto)
      apply (subgoal_tac "\<alpha> r1 \<subseteq> UNDASHED \<union> DASHED")
      apply (metis DASHED_DASHED_TWICE_contra UNDASHED_DASHED_TWICE_contra Un_iff set_mp)
      apply (simp add: WF_RELATION_UNDASHED_DASHED)
      apply (simp add: closure)
    done

    moreover from assms have "UNREST (VAR - \<alpha> r2) (\<pi> r2)"
      by (simp add: closure)

    moreover with assms have "UNREST DASHED_TWICE (\<pi> r2)"
      apply (rule_tac UNREST_subset)
      apply (auto)
      apply (subgoal_tac "\<alpha> r2 \<subseteq> UNDASHED \<union> DASHED")
      apply (metis DASHED_not_DASHED_TWICE UNDASHED_DASHED_TWICE_contra UnE in_mono)
      apply (simp add: WF_RELATION_UNDASHED_DASHED)
      apply (simp add: closure)
    done

    moreover
    from assms have "(VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))
                     \<subseteq> VAR - (in (\<alpha> r1) \<union> dash ` out (\<alpha> r1))"
      by (auto simp add: out_alphabet_def)

    moreover
    from assms have "(VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))
                     \<subseteq> VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))"
      by (auto simp add: in_alphabet_def)

    moreover
    with assms have "UNREST (SS1 ` (VAR - \<alpha> r1)) (\<pi> r1[SS1])"
      apply (rule_tac UNREST_SubstP)
      apply (simp_all add: closure)
    done

    moreover
    with assms have "UNREST (SS1 ` VAR - SS1 ` (\<alpha> r1)) (\<pi> r1[SS1])"
      apply (subgoal_tac "inj SS1")
      apply (metis image_set_diff)
      apply (metis SS1_VAR_SUBST SS1_inv VAR_SUBST_inv_ss_app inj_on_def)
    done

    moreover
    with assms have "UNREST (VAR - (in (\<alpha> r1) \<union> dash ` out (\<alpha> r1))) (\<pi> r1[SS1])"
      apply (simp add: WF_RELATION_unfold)
      apply (simp add: closure SS1_UNDASHED_DASHED_image)
      apply (subgoal_tac "surj SS1")
      apply (simp add: VAR_def)
      apply (insert SS1_VAR_SUBST)
      apply (simp add: VAR_SUBST_def bij_def)
    done

    moreover
    with calculation assms have "UNREST ((VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))) (\<pi> r1[SS1])"
      apply (rule_tac ?vs1.0="VAR - (in (\<alpha> r1) \<union> dash ` out (\<alpha> r1))" in UNREST_subset)
      apply (auto simp add: closure)
    done

    moreover
    with assms have "UNREST (SS2 ` (VAR - \<alpha> r2)) (\<pi> r2[SS2])"
      apply (rule_tac UNREST_SubstP)
      apply (simp_all add: closure)
    done

    moreover
    from assms have "SS2 ` (VAR - \<alpha> r2) = VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))"
    proof -
      have "SS2 ` (VAR - \<alpha> r2) = SS2 ` VAR - SS2 ` (\<alpha> r2)"
        by (metis image_set_diff SS2_VAR_SUBST VAR_SUBST_bij bij_betw_imp_inj_on)

      also from assms have "... = VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))"
        apply (simp add: WF_RELATION_unfold)
        apply (simp add: closure SS2_UNDASHED_DASHED_image VAR_def)
        apply (insert SS2_VAR_SUBST)
        apply (simp add: VAR_SUBST_def bij_def)
      done

      ultimately show ?thesis by simp
    qed

    moreover
    with calculation assms have "UNREST ((VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))) (\<pi> r2[SS2])"
      apply (rule_tac ?vs1.0="VAR - (dash ` dash ` in (\<alpha> r2) \<union> out (\<alpha> r2))" in UNREST_subset)
      apply (auto simp add: closure)
    done

    moreover from assms calculation have "UNREST (((VAR - DASHED_TWICE) - (in (\<alpha> r1) \<union> out (\<alpha> r2))) \<union> DASHED_TWICE) (\<exists>p DASHED_TWICE . ((\<pi> r1[SS1]) \<and>p (\<pi> r2[SS2])))"
      apply (rule_tac UNREST_ExistsP)
      apply (simp add: closure)
      apply (rule_tac UNREST_AndP)
      apply (simp_all add: closure)
    done

    ultimately show ?thesis using assms
      apply (simp add: WF_PREDICATE_OVER_def closure)
      apply (subgoal_tac "UNREST DASHED_TWICE (\<pi> r1)")
      apply (subgoal_tac "UNREST DASHED_TWICE (\<pi> r2)")
      apply (simp add: SemiR_algebraic closure)
      apply (subgoal_tac "VAR - DASHED_TWICE - (in (\<alpha> r1) \<union> out (\<alpha> r2)) \<union> DASHED_TWICE =
                          VAR - (in (\<alpha> r1) \<union> out (\<alpha> r2))")
      apply (force)
      apply (subgoal_tac "(in (\<alpha> r1) \<union> out (\<alpha> r2)) \<inter> DASHED_TWICE = {}")
      apply (force)
      apply (safe)
      apply (simp add: alphabet_defs)
      apply (simp add: alphabet_defs)
    done
  qed

  ultimately show ?thesis using assms
    by (auto simp add: SemiA_def WF_RELATION_unfold WF_ALPHA_PREDICATE_def alphabet_defs)
qed

subsection {* Alphabet Theorems *}

theorem SkipA_alphabet [alphabet] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 \<alpha> (II\<alpha> a) = a"
apply (simp add: SkipA_def)
done

theorem AssignA_alphabet [alphabet] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 \<alpha> (x :=\<^bsub>a\<^esub> v) = a"
  by (simp add: AssignA_def)

theorem CondA_alphabet [alphabet] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 (\<alpha> r1) = (\<alpha> r2);
 (\<alpha> b) \<subseteq> (\<alpha> r1)\<rbrakk> \<Longrightarrow>
 \<alpha> (r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2) = (\<alpha> r1)"
apply (simp add: CondA_def)
done

theorem SemiA_alphabet [alphabet] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 \<alpha> (r1 ;\<alpha> r2) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
apply (simp add: SemiA_def)
done

subsection {* Evaluation Theorems *}

theorem EvalP_SkipP_override :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 vs \<subseteq> NON_REL_VAR\<rbrakk> \<Longrightarrow>
 \<lbrakk>II\<rbrakk>(b1 \<oplus> b2 on vs) = \<lbrakk>II\<rbrakk>b1"
apply (simp add: SkipR_def)
apply (simp add: EvalP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "v" in bspec)
apply (assumption)
apply (subgoal_tac "v \<notin> vs", simp)
apply (subgoal_tac "dash v \<notin> vs", simp)
apply (auto simp: NON_REL_VAR_def) [1]
apply (auto simp: NON_REL_VAR_def) [1]
-- {* Subgoal 2 *}
apply (simp add: closure)
-- {* Subgoal 3 *}
apply (subgoal_tac "v \<notin> vs", simp)
apply (subgoal_tac "dash v \<notin> vs", simp)
apply (auto simp: NON_REL_VAR_def) [1]
apply (auto simp: NON_REL_VAR_def) [1]
done

theorem EvalA_SkipA [evala] :
"a \<in> REL_ALPHABET \<Longrightarrow> \<lbrakk>II\<alpha> a\<rbrakk>\<pi> = II a"
  by (simp add:EvalA_def SkipA_def)

(*
theorem EvalA_SkipA [evala] :
"\<lbrakk>II\<alpha> (UNDASHED \<union> DASHED)\<rbrakk>\<pi> = II"
apply (simp add: EvalA_def)
apply (subgoal_tac "UNDASHED \<union> DASHED \<in> REL_ALPHABET")
apply (simp add: SkipA_def)
apply (utp_pred_tac)
apply (safe)
apply (subgoal_tac "VAR - (UNDASHED \<union> DASHED) \<subseteq> NON_REL_VAR")
apply (simp add: EvalP_SkipP_override)
apply (simp add: NON_REL_VAR_def)
apply (rule_tac x = "b" in bexI)
apply (simp)
apply (assumption)
apply (simp add: REL_ALPHABET_def WF_ALPHABET_def)
-- {* Fails because @{term UNDASHED} and  @{term DASHED} are not alphabets. *}
oops
*)

theorem EvalA_CondA [evala] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 (\<alpha> r1) = (\<alpha> r2);
 (\<alpha> b) \<subseteq> (\<alpha> r1)\<rbrakk> \<Longrightarrow>
 \<lbrakk>r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2\<rbrakk>\<pi> = \<lbrakk>r1\<rbrakk>\<pi> \<triangleleft> \<lbrakk>b\<rbrakk>\<pi> \<triangleright> \<lbrakk>r2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: CondA_def)
done

theorem EvalA_SemiA [evala] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 \<lbrakk>r1 ;\<alpha> r2\<rbrakk>\<pi> = \<lbrakk>r1\<rbrakk>\<pi> ; \<lbrakk>r2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: SemiA_def)
done

subsubsection {* Proof Experiments *}

theorem SemiA_assoc :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 (r1 ;\<alpha> r2) ;\<alpha> r3 = r1 ;\<alpha> (r2 ;\<alpha> r3)"
apply (utp_alpha_tac)
apply (rule conjI)
apply (utp_alphabet_tac) [1]
apply (utp_rel_auto_tac) [1]
done

theorem SemiA_OrA_distl :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 ;\<alpha> (r2 \<or>\<alpha> r3) = (r1 ;\<alpha> r2) \<or>\<alpha> (r1 ;\<alpha> r3)"
apply (utp_alpha_tac)
apply (rule conjI)
apply (utp_alphabet_tac) [1]
apply (utp_rel_auto_tac) [1]
done

theorem SemiA_OrA_distr :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 (r1 \<or>\<alpha> r2) ;\<alpha> r3 = (r1 ;\<alpha> r3) \<or>\<alpha> (r2 ;\<alpha> r3)"
apply (utp_alpha_tac)
apply (rule conjI)
apply (utp_alphabet_tac) [1]
apply (utp_rel_auto_tac) [1]
done

theorem SemiP_SkipR_left:
  assumes "r \<in> WF_RELATION" "a \<in> HOM_ALPHABET" "out a = dash ` in (\<alpha> r)"
  shows "II\<alpha> a ;\<alpha> r = r"
proof -

  from assms have ina:"in a = in (\<alpha> r)"
    apply (simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def)
    apply (metis undash_dash_image)
  done
    
  moreover with assms(1) have "in a \<union> out (\<alpha> r) = \<alpha> r"
    by (simp add:WF_RELATION_def REL_ALPHABET_def in_out_union)

  moreover from assms have "II a ; (\<pi> r) = (\<pi> r)"
  proof -
    have "undash ` (DASHED - dash ` in (\<alpha> r)) = UNDASHED - in (\<alpha> r)"
    proof -  
      have "dash ` in (\<alpha> r) \<subseteq> DASHED"
        by (metis out_dash out_DASHED)

      thus ?thesis
        by (simp add: inj_on_image_set_diff[OF undash_inj_on_DASHED])
    qed

    with assms show ?thesis
      apply (simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def)
      apply (rule_tac SemiP_SkipRA_left)
      apply (simp_all add:closure ina)
      apply (force intro:UNREST_subset simp add:closure alphabet_defs)+
    done
  qed

  ultimately show ?thesis using assms
    by (utp_alpha_tac, simp add: EvalA_def)
qed

theorem SemiP_SkipR_right:
  assumes "r \<in> WF_RELATION" "a \<in> HOM_ALPHABET" "in a = undash ` out (\<alpha> r)"
  shows "r ;\<alpha> II\<alpha> a = r"
proof -
  from assms have ina:"out a = out (\<alpha> r)"
    apply (simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def)
    apply (metis dash_undash_image out_DASHED)
  done
    
  moreover with assms(1) have "in (\<alpha> r) \<union> out (\<alpha> r) = \<alpha> r"
    by (metis WF_RELATION_unfold in_out_union sup_commute)

  moreover from assms have "(\<pi> r) ; II a = (\<pi> r)"
  proof -
    have "dash ` (UNDASHED - undash ` out (\<alpha> r)) = DASHED - out (\<alpha> r)"
      by (simp add: inj_on_image_set_diff[OF dash_inj] dash_UNDASHED_image dash_undash_image out_DASHED)

    with assms show ?thesis
      apply (simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def)
      apply (rule_tac SemiP_SkipRA_right)
      apply (simp_all add:closure ina)
      apply (force intro:UNREST_subset simp add:closure alphabet_defs)+
    done
  qed

  ultimately show ?thesis using assms
    by (utp_alpha_tac, simp add: EvalA_def)
qed

end

context ALPHA_PRED_BOOL
begin

theorem VarA_rel_closure [closure] :
"x \<in> UNDASHED \<union> DASHED \<Longrightarrow>
VarA x \<in> WF_RELATION"
apply (simp add:WF_RELATION_def REL_ALPHABET_def)
apply (simp add:alphabet closure)
done
end

end