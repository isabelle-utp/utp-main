(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_rel.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Relations *}

theory utp_rel
imports utp_pred utp_subst
begin

context PRED
begin

subsection {* Composable Bindings *}

definition NON_REL_VAR :: "'TYPE VAR set" where
"NON_REL_VAR = VAR - (UNDASHED \<union> DASHED)"

definition COMPOSABLE ::
  "(('VALUE, 'TYPE) BINDING \<times>
    ('VALUE, 'TYPE) BINDING) set" where
"COMPOSABLE = {(b1, b2) .
   (\<forall> v \<in> UNDASHED . b1(dash v) = b2 v) \<and> b1 \<cong> b2 on NON_REL_VAR}"

subsection {* Substitutions *}

text {* The substitution @{term "SS"} swaps dashed and undashed variables. *}

definition SS :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS = (\<lambda> v .
   if v \<in> UNDASHED then (dash v) else
   if v \<in> DASHED then (undash v) else v)"

definition SS1 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS1 = (\<lambda> v .
 if (v \<in> DASHED) then (dash v) else
 if (v \<in> DASHED_TWICE) then (undash v) else v)"

definition SS2 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS2 = (\<lambda> v .
 if v \<in> UNDASHED then dash (dash v) else
 if v \<in> DASHED_TWICE then undash (undash v) else v)"

subsection {* Operators *}

subsubsection {* Skip *}

definition SkipR :: "('VALUE, 'TYPE) PREDICATE" where
"SkipR = {b \<in> WF_BINDING . \<forall> v \<in> UNDASHED . b v = b (dash v)}"

notation SkipR ("II")

subsubsection {* Sequence *}

definition SemiR ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 SemiR p1 p2 = {b1 \<oplus> b2 on DASHED | b1 b2 .
   b1 \<in> p1 \<and> b2 \<in> p2 \<and> (b1, b2) \<in> COMPOSABLE}"

(* Not sure about the precedence of sequential composition yet. *)

notation SemiR (infixr ";" 140)

text {* Algebraic version of sequential composition *}

definition SemiR2 ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<and>
 UNREST DASHED_TWICE p1 \<and>
 UNREST DASHED_TWICE p2 \<longrightarrow>
 SemiR2 p1 p2 = (\<exists>p DASHED_TWICE . p1[SS1] \<and>p p2[SS2])"

subsubsection {* Conditional *}

text {* Should we impose a constraint on b for it to be a condition? *}

definition CondR ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<and>
 b \<in> WF_PREDICATE \<longrightarrow>
 CondR p1 b p2 = (b \<and>p p1) \<or>p (\<not>p b \<and>p p2)"

notation CondR ("_ \<triangleleft> _ \<triangleright> _")

subsection {* Theorems *}

subsubsection {* Substitution Theorems *}

text {* Theorems for @{term SS} *}

theorem SS_UNDASHED_app :
"\<lbrakk>x \<in> UNDASHED\<rbrakk> \<Longrightarrow> SS x = dash x"
apply (simp add: SS_def)
done

theorem SS_DASHED_app :
"\<lbrakk>x \<in> DASHED\<rbrakk> \<Longrightarrow> SS x = undash x"
apply (simp add: SS_def)
apply (simp add: var_defs)
done

theorem SS_DASHED_TWICE_app :
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS x = x"
apply (simp add: SS_def)
apply (simp add: var_defs)
done

theorem SS_ident_app :
"\<lbrakk>\<not> x \<in> UNDASHED; \<not> x \<in> DASHED\<rbrakk> \<Longrightarrow> SS x = x"
apply (simp add: SS_def)
done

theorems SS_simps =
  SS_UNDASHED_app
  SS_DASHED_app
  SS_DASHED_TWICE_app
  SS_ident_app

theorem SS_VAR_SUBST [closure] :
"SS \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (simp add: bij_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (simp add: inj_on_def)
apply (simp add: SS_def)
apply (safe)
apply (auto)
-- {* Subgoal 1.1 *}
apply (insert undash_inj_on_DASHED) [1]
apply (simp add: inj_on_eq_iff)
-- {* Subgoal 1.2 *}
apply (insert dash_inj) [1]
apply (simp add: inj_on_eq_iff)
-- {* Subgoal 2 *}
apply (simp add: image_def)
apply (rule_tac x = "SS x" in exI)
apply (simp add: SS_def)
apply (auto) [1]
  -- {* Subgoal 4 *}
apply (simp add: SS_def)
done

theorem SS_VAR_SUBST_ON [closure] :
"SS \<in> VAR_SUBST_ON (UNDASHED \<union> DASHED)"
apply (simp add: VAR_SUBST_ON_def)
apply (simp add: SS_VAR_SUBST)
apply (simp add: SS_def)
done

theorem SS_VAR_SUBST_INV [closure] :
"SS \<in> VAR_SUBST_INV"
apply (simp add: VAR_SUBST_INV_def)
apply (simp add: SS_VAR_SUBST)
apply (rule sym [OF inv_equality])
apply (simp_all add: SS_def)
apply (auto)
done

theorem SS_inv [simp] :
"inv SS = SS"
apply (insert SS_VAR_SUBST_INV)
apply (simp add: VAR_SUBST_INV_def)
done

theorem SS_DASHED_member :
"x \<in> DASHED \<Longrightarrow> \<not> SS x \<in> DASHED"
apply (simp add: SS_def)
apply (simp add: var_defs)
done

text {* Theorems for @{term SS1} *}

theorem SS1_UNDASHED_app :
"\<lbrakk>x \<in> UNDASHED\<rbrakk> \<Longrightarrow> SS1 x = x"
apply (simp add: SS1_def)
done

theorem SS1_DASHED_app :
"\<lbrakk>x \<in> DASHED\<rbrakk> \<Longrightarrow> SS1 x = dash x"
apply (simp add: SS1_def)
done

theorem SS1_DASHED_TWICE_app :
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS1 x = undash x"
apply (simp add: SS1_def)
apply (simp add: var_defs)
done

theorem SS1_ident_app :
"\<lbrakk>\<not> x \<in> DASHED; \<not> x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS1 x = x"
apply (simp add: SS1_def)
done

theorems SS1_simps =
  SS1_UNDASHED_app
  SS1_DASHED_app
  SS1_DASHED_TWICE_app
  SS1_ident_app

theorem SS1_VAR_SUBST [closure] :
"SS1 \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (simp add: bij_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (simp add: inj_on_def)
apply (simp add: SS1_def)
apply (safe)
apply (auto)
-- {* Subgoal 1.1 *}
apply (insert undash_inj_on_DASHED_TWICE) [1]
apply (simp add: inj_on_eq_iff)
-- {* Subgoal 1.2 *}
apply (insert dash_inj) [1]
apply (simp add: inj_on_eq_iff)
-- {* Subgoal 2 *}
apply (simp add: image_def)
apply (rule_tac x = "SS1 x" in exI)
apply (simp add: SS1_def)
apply (auto) [1]
  -- {* Subgoal 4 *}
apply (simp add: SS1_def)
done

theorem SS1_VAR_SUBST_ON [closure] :
"SS1 \<in> VAR_SUBST_ON (DASHED \<union> DASHED_TWICE)"
apply (simp add: VAR_SUBST_ON_def)
apply (simp add: SS1_VAR_SUBST)
apply (simp add: SS1_def)
done

theorem SS1_VAR_SUBST_INV [closure] :
"SS1 \<in> VAR_SUBST_INV"
apply (simp add: VAR_SUBST_INV_def)
apply (simp add: SS1_VAR_SUBST)
apply (rule sym [OF inv_equality])
apply (simp_all add: SS1_def)
apply (auto)
done

theorem SS1_inv [simp] :
"inv SS1 = SS1"
apply (insert SS1_VAR_SUBST_INV)
apply (simp add: VAR_SUBST_INV_def)
done

text {* Theorems for @{term SS2} *}

theorem SS2_DASHED_app :
"x \<in> DASHED \<Longrightarrow> SS2 x = x"
apply (simp add: SS2_def)
apply (simp add: var_defs)
done

theorem SS2_UNDASHED_app :
"x \<in> UNDASHED \<Longrightarrow> SS2 x = dash (dash x)"
apply (simp add: SS2_def)
done

theorem SS2_DASHED_TWICE_app :
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS2 x =  undash (undash x)"
apply (simp add: SS2_def)
apply (simp add: var_defs)
done

theorem SS2_ident_app :
"\<lbrakk>\<not> x \<in> UNDASHED; \<not> x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS2 x = x"
apply (simp add: SS2_def)
done

theorems SS2_simps =
  SS2_UNDASHED_app
  SS2_DASHED_app
  SS2_DASHED_TWICE_app
  SS2_ident_app

theorem SS2_VAR_SUBST [closure] :
"SS2 \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (simp add: bij_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (simp add: inj_on_def)
apply (simp add: SS2_def)
apply (safe)
apply (auto)
-- {* Subgoal 1.1 *}
apply (insert undash_inj_on_DASHED undash_inj_on_DASHED_TWICE) [1]
apply (simp add: inj_on_eq_iff)
-- {* Subgoal 1.2 *}
apply (insert dash_inj) [1]
apply (simp add: inj_on_eq_iff)
-- {* Subgoal 2 *}
apply (simp add: image_def)
apply (rule_tac x = "SS2 x" in exI)
apply (simp add: SS2_def)
apply (auto) [1]
  -- {* Subgoal 4 *}
apply (simp add: SS2_def)
done

theorem SS2_VAR_SUBST_ON [closure] :
"SS2 \<in> VAR_SUBST_ON (UNDASHED \<union> DASHED_TWICE)"
apply (simp add: VAR_SUBST_ON_def)
apply (simp add: SS2_VAR_SUBST)
apply (simp add: SS2_def)
done

theorem SS2_VAR_SUBST_INV [closure] :
"SS2 \<in> VAR_SUBST_INV"
apply (simp add: VAR_SUBST_INV_def)
apply (simp add: SS2_VAR_SUBST)
apply (rule sym [OF inv_equality])
apply (simp_all add: SS2_def)
apply (auto)
done

theorem SS2_inv [simp] :
"inv SS2 = SS2"
apply (insert SS2_VAR_SUBST_INV)
apply (simp add: VAR_SUBST_INV_def)
done

subsubsection {* Theorems for @{term "COMPOSABLE"} *}

theorem COMPOSABLE_dash [intro] :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE; x \<in> UNDASHED\<rbrakk> \<Longrightarrow> b1(dash x) = b2 x"
apply (simp add: COMPOSABLE_def)
done

theorem COMPOSABLE_ident [intro] :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE; \<not> x \<in> UNDASHED; \<not> x \<in> DASHED\<rbrakk> \<Longrightarrow> b1 x = b2 x"
apply (simp only: COMPOSABLE_def)
apply (simp add: NON_REL_VAR_def)
apply (simp add: binding_equiv_def)
done

subsubsection {* Closure Theorems *}

theorem SkipR_closure [closure] :
"II \<in> WF_PREDICATE"
apply (simp add: SkipR_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem CondR_closure [closure] :
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<and>
 b \<in> WF_PREDICATE \<longrightarrow>
 p1 \<triangleleft> b \<triangleright> p2 \<in> WF_PREDICATE"
apply (simp add: CondR_def)
apply (simp add: closure)
done

theorem SemiR_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 ; p2 \<in> WF_PREDICATE"
apply (simp add: SemiR_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

subsection {* Validation of Soundness *}

lemma SemiR_Semi2R_equiv_lemma1 :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (b1, b2) \<in> COMPOSABLE\<rbrakk> \<Longrightarrow>
 ((b1 \<oplus> b2 on DASHED) \<oplus> (SubstB SS1 b1) on DASHED_TWICE) \<circ> SS1 =
   b1 \<oplus> (SubstB SS1 b2) on DASHED_TWICE"
apply (rule ext)
apply (simp add: SubstB_def closure)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
done

lemma SemiR_Semi2R_equiv_lemma2 :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (b1, b2) \<in> COMPOSABLE\<rbrakk> \<Longrightarrow>
 ((b1 \<oplus> b2 on DASHED) \<oplus> (SubstB SS1 b1) on DASHED_TWICE) \<circ> SS2 =
   b2 \<oplus> (SubstB SS2 b1) on DASHED_TWICE"
apply (rule ext)
apply (simp add: SubstB_def closure)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: COMPOSABLE_dash)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
apply (simp add: COMPOSABLE_ident)
done

theorem SemiR_SemiR2_equiv :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST DASHED_TWICE p1;
 UNREST DASHED_TWICE p2\<rbrakk> \<Longrightarrow>
 SemiR p1 p2 = SemiR2 p1 p2"
apply (rule sym)
apply (simp add: SemiR2_def)
apply (utp_pred_tac)
apply (simp add: EvalP_def)
apply (simp add: SemiR_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x =
  "SubstB (inv SS1) (b \<oplus> b' on DASHED_TWICE) \<oplus> b on DASHED_TWICE" in exI)
apply (rule_tac x =
  "SubstB (inv SS2) (b \<oplus> b' on DASHED_TWICE) \<oplus> b on DASHED_TWICE" in exI)
apply (safe)
-- {* Subgoal 1.1 *}
apply (simp add: SubstB_def closure)
apply (rule ext)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
-- {* Subgoal 1.2 *}
apply (auto intro: UNREST_member) [1]
-- {* Subgoal 1.3 *}
apply (auto intro: UNREST_member) [1]
-- {* Subgoal 1.3 *}
apply (simp add: SubstB_def closure)
apply (simp add: COMPOSABLE_def)
apply (safe)
apply (simp add: SS1_simps SS2_simps)
apply (simp add: binding_equiv_def)
apply (simp add: NON_REL_VAR_def)
apply (rule ballI)
apply (clarsimp)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
-- {* Subgoal 2 *}
apply (simp add: SubstB_def closure)
apply (rule_tac x = "SubstB SS1 b1" in bexI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (simp add: SemiR_Semi2R_equiv_lemma1)
apply (auto intro: UNREST_member simp: closure) [1]
-- {* Subgoal 2.2 *}
apply (simp add: SemiR_Semi2R_equiv_lemma2)
apply (auto intro: UNREST_member simp: closure) [1]
-- {* Subgoal 2.3 *}
apply (simp add: closure)
done
end
end