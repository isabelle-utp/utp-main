(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_rel.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Relations *}

theory utp_rel
imports utp_pred utp_expr utp_rename utp_unrest "../tactics/utp_expr_tac"
begin

subsection {* Composable Bindings *}

definition NON_REL_VAR :: "'VALUE VAR set" where
"NON_REL_VAR = - (UNDASHED \<union> DASHED)"

definition COMPOSABLE_BINDINGS ::
  "('VALUE WF_BINDING \<times>
    'VALUE WF_BINDING) set" where
"COMPOSABLE_BINDINGS =
 {(b1, b2) . (\<forall> v \<in> UNDASHED . \<langle>b1\<rangle>\<^sub>b(dash v) = \<langle>b2\<rangle>\<^sub>b v) \<and> b1 \<cong> b2 on NON_REL_VAR}"

subsection {* Renamings *}

text {* The renaming @{term "SS"} swaps dashed and undashed variables. *}

lift_definition SS :: "'VALUE VAR_RENAME" is
"(\<lambda> v .
   if v \<in> UNDASHED then (dash v) else
   if v \<in> DASHED then (undash v) else v)"
  by (auto simp add:VAR_RENAME_def bij_def inj_on_def)

lift_definition SS1 :: "'VALUE VAR_RENAME" is
"(\<lambda> v .
   if (v \<in> DASHED) then (dash v) else
   if (v \<in> DASHED_TWICE) then (undash v) else v)"
  by (auto simp add: VAR_RENAME_def bij_def inj_on_def)

lift_definition SS2 :: "'VALUE VAR_RENAME" is
"(\<lambda> v .
   if v \<in> UNDASHED then dash (dash v) else
   if v \<in> DASHED_TWICE then undash (undash v) else v)"
  apply (auto simp add: VAR_RENAME_def bij_def inj_on_def)
  apply (metis (lifting) DASHED_TWICE_undash_DASHED dash_undash_DASHED dash_undash_DASHED_TWICE)
  apply (auto simp add: image_def)[1]
  apply (drule_tac x="dash (dash x)" in bspec) back
  apply (auto)
  apply (auto simp add: image_def)[1]
  apply (drule_tac x="x" in bspec) back
  apply (auto)
  apply (metis (lifting) DASHED_TWICE_undash_DASHED DASHED_undash_UNDASHED dash_undash_DASHED dash_undash_DASHED_TWICE)
done

subsection {* Operators *}

subsubsection {* Skip *}

lift_definition SkipR :: "'VALUE WF_PREDICATE"
is "{b. \<forall> v \<in> UNDASHED . \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (dash v)}"
done

notation SkipR ("II")

subsubsection {* Alphabet Skip *}

lift_definition SkipRA :: "'VALUE VAR set \<Rightarrow> 'VALUE WF_PREDICATE" is
"\<lambda> vs. (\<exists>p ((UNDASHED \<union> DASHED) - vs). II)"
done

notation SkipRA ("II")

subsubsection {* Conditional *}

text {* Should we impose a constraint on b for it to be a condition? *}

definition CondR ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"CondR p1 b p2 = (b \<and>p p1) \<or>p (\<not>p b \<and>p p2)"

notation CondR ("_ \<triangleleft> _ \<triangleright> _")

subsubsection {* Sequential Composition *}

lift_definition SemiR ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" is
"\<lambda> p1 p2.
 {b1 \<oplus>\<^sub>b b2 on DASHED | b1 b2 .
   b1 \<in> p1 \<and> b2 \<in> p2 \<and> (b1, b2) \<in> COMPOSABLE_BINDINGS}"
done

(* Not sure about the precedence of sequential composition yet. *)

notation SemiR (infixr ";" 140)

subsubsection {* Assignment *}

definition AssignR ::
"'VALUE VAR \<Rightarrow>
 'VALUE VAR set \<Rightarrow>
 'VALUE WF_EXPRESSION \<Rightarrow>
 'VALUE WF_PREDICATE" where
"AssignR x a v \<equiv> VarE (dash x) ==p v \<and>p II (a - {x,dash x})"

notation AssignR ("_ :=p\<^bsub>_ \<^esub>_" [190] 190)

subsection {* Theorems *}

subsubsection {* Renaming Theorems *}

text {* Theorems for @{term SS} *}

theorem SS_UNDASHED_app :
"\<lbrakk>x \<in> UNDASHED\<rbrakk> \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s x = dash x"
apply (simp add: SS.rep_eq)
done

theorem SS_DASHED_app :
"\<lbrakk>x \<in> DASHED\<rbrakk> \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s x = undash x"
apply (simp add: SS.rep_eq)
apply (simp add: var_defs)
done

theorem SS_DASHED_TWICE_app :
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s x = x"
apply (simp add: SS.rep_eq)
apply (simp add: var_defs)
done

theorem SS_ident_app :
"\<lbrakk>\<not> x \<in> UNDASHED; \<not> x \<in> DASHED\<rbrakk> \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s x = x"
apply (simp add: SS.rep_eq)
done

theorem SS_VAR_RENAME_ON [closure] :
"SS \<in> VAR_RENAME_ON (UNDASHED \<union> DASHED)"
  by (simp add: VAR_RENAME_ON_def SS.rep_eq)

theorem SS_VAR_RENAME_INV [closure] :
"SS \<in> VAR_RENAME_INV"
apply (simp add: VAR_RENAME_INV_def)
apply (rule Rep_VAR_RENAME_intro)
apply (simp add:SS.rep_eq)
apply (rule sym [OF inv_equality])
apply (auto)
done

theorem SS_inv [simp] :
"inv\<^sub>s SS = SS"
apply (insert SS_VAR_RENAME_INV)
apply (simp add: VAR_RENAME_INV_def VAR_RENAME_def)
apply (metis (lifting) SS_VAR_RENAME_INV VAR_RENAME_INV_inv)
done

theorem SS_inv' [simp] :
"inv \<langle>SS\<rangle>\<^sub>s = \<langle>SS\<rangle>\<^sub>s"
  apply (insert SS_inv)
  apply (erule Rep_VAR_RENAME_elim)
  apply (simp only: rename_inv_rep_eq)
done

theorem SS_UNDASHED_DASHED_image [urename]:
"\<lbrakk>vs \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 SS `\<^sub>s vs = dash ` (in vs) \<union> undash ` (out vs)"
  by (auto simp add: image_def var_defs SS.rep_eq)

theorem SS_DASHED_member :
"x \<in> DASHED \<Longrightarrow> \<not> \<langle>SS\<rangle>\<^sub>s x \<in> DASHED"
apply (simp add: SS.rep_eq)
apply (simp add: var_defs)
done

theorems SS_simps =
  SS_UNDASHED_app
  SS_DASHED_app
  SS_DASHED_TWICE_app
  SS_ident_app
  SS_inv
  SS_UNDASHED_DASHED_image

text {* Theorems for @{term SS1} *}

theorem SS1_UNDASHED_app [urename]:
"\<lbrakk>x \<in> UNDASHED\<rbrakk> \<Longrightarrow> \<langle>SS1\<rangle>\<^sub>s x = x"
  by (simp add: SS1.rep_eq)

theorem SS1_DASHED_app [urename]:
"\<lbrakk>x \<in> DASHED\<rbrakk> \<Longrightarrow> \<langle>SS1\<rangle>\<^sub>s x = dash x"
apply (simp add: SS1.rep_eq)
done

theorem SS1_DASHED_TWICE_app [urename]:
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> \<langle>SS1\<rangle>\<^sub>s x = undash x"
apply (simp add: SS1.rep_eq)
apply (simp add: var_defs)
done

theorem SS1_ident_app [urename]:
"\<lbrakk>\<not> x \<in> DASHED; \<not> x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> \<langle>SS1\<rangle>\<^sub>s x = x"
apply (simp add: SS1.rep_eq)
done

theorem SS1_VAR_RENAME_ON [closure] :
"SS1 \<in> VAR_RENAME_ON (DASHED \<union> DASHED_TWICE)"
apply (simp add: VAR_RENAME_ON_def)
apply (simp add: SS1.rep_eq)
done

theorem SS1_VAR_RENAME_INV [closure] :
"SS1 \<in> VAR_RENAME_INV"
apply (simp add: VAR_RENAME_INV_def)
apply (rule Rep_VAR_RENAME_intro)
apply (simp add:SS1.rep_eq)
apply (rule sym [OF inv_equality])
apply (auto)
done

theorem SS1_inv [simp] :
"inv\<^sub>s SS1 = SS1"
apply (insert SS1_VAR_RENAME_INV)
apply (simp add: VAR_RENAME_INV_def VAR_RENAME_def)
apply (metis (lifting) SS1_VAR_RENAME_INV VAR_RENAME_INV_inv)
done

theorem SS1_inv' [simp] :
"inv \<langle>SS1\<rangle>\<^sub>s = \<langle>SS1\<rangle>\<^sub>s"
  apply (insert SS1_inv)
  apply (erule Rep_VAR_RENAME_elim)
  apply (simp only: rename_inv_rep_eq)
done

theorem SS1_UNDASHED_DASHED_image [urename] :
"\<lbrakk>vs \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 SS1 `\<^sub>s vs = (in vs) \<union> dash ` (out vs)"
  by (auto simp add: image_def var_defs SS1.rep_eq)

theorems SS1_simps =
  SS1_UNDASHED_app
  SS1_DASHED_app
  SS1_DASHED_TWICE_app
  SS1_ident_app
  SS1_UNDASHED_DASHED_image

text {* Theorems for @{term SS2} *}

theorem SS2_DASHED_app [urename]:
"x \<in> DASHED \<Longrightarrow> \<langle>SS2\<rangle>\<^sub>s x = x"
apply (simp add: SS2.rep_eq)
apply (simp add: var_defs)
done

theorem SS2_UNDASHED_app [urename]:
"x \<in> UNDASHED \<Longrightarrow> \<langle>SS2\<rangle>\<^sub>s x = dash (dash x)"
apply (simp add: SS2.rep_eq)
done

theorem SS2_DASHED_TWICE_app [urename]:
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> \<langle>SS2\<rangle>\<^sub>s x =  undash (undash x)"
apply (simp add: SS2.rep_eq)
apply (simp add: var_defs)
done

theorem SS2_ident_app [urename]:
"\<lbrakk>\<not> x \<in> UNDASHED; \<not> x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> \<langle>SS2\<rangle>\<^sub>s x = x"
apply (simp add: SS2.rep_eq)
done

theorem SS2_VAR_RENAME_ON [closure] :
"SS2 \<in> VAR_RENAME_ON (UNDASHED \<union> DASHED_TWICE)"
  by (simp add: VAR_RENAME_ON_def SS2.rep_eq)

theorem SS2_VAR_RENAME_INV [closure] :
"SS2 \<in> VAR_RENAME_INV"
  apply (simp add: VAR_RENAME_INV_def)
  apply (rule Rep_VAR_RENAME_intro)
  apply (simp add:SS2.rep_eq)
  apply (rule sym [OF inv_equality])
  apply (auto)
done

theorem SS2_inv [simp] :
"inv\<^sub>s SS2 = SS2"
apply (insert SS2_VAR_RENAME_INV)
apply (simp add: VAR_RENAME_INV_def VAR_RENAME_def)
apply (metis (lifting) SS2_VAR_RENAME_INV VAR_RENAME_INV_inv)
done

theorem SS2_inv' [simp] :
"inv \<langle>SS2\<rangle>\<^sub>s = \<langle>SS2\<rangle>\<^sub>s"
  apply (insert SS2_inv)
  apply (erule Rep_VAR_RENAME_elim)
  apply (simp only: rename_inv_rep_eq)
done

theorem SS2_UNDASHED_DASHED_image [urename]:
"\<lbrakk>vs \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 SS2 `\<^sub>s vs = dash ` dash ` (in vs) \<union> (out vs)"
  by (auto simp add: image_def var_defs SS2.rep_eq)

theorems SS2_simps =
  SS2_UNDASHED_app
  SS2_DASHED_app
  SS2_DASHED_TWICE_app
  SS2_ident_app
  SS2_UNDASHED_DASHED_image

subsubsection {* Renamings Equalities *}

lemma SS1_SS_eq_SS2: "SS1 \<circ>\<^sub>s SS \<cong>\<^sub>s SS2 on UNDASHED"
  by (auto simp add:rename_equiv_def SS1.rep_eq SS.rep_eq SS2.rep_eq)

lemma SS2_SS_eq_SS1: "SS2 \<circ>\<^sub>s SS \<cong>\<^sub>s SS1 on DASHED"
  by (auto simp add:rename_equiv_def SS1.rep_eq SS.rep_eq SS2.rep_eq)

lemma SS1_eq_id: "SS1 \<cong>\<^sub>s id\<^sub>s on UNDASHED"
  by (auto simp add:rename_equiv_def SS1.rep_eq)

lemma SS2_eq_id: "SS2 \<cong>\<^sub>s id\<^sub>s on DASHED"
  by (auto simp add:rename_equiv_def SS2.rep_eq)

subsubsection {* Theorems for @{term "COMPOSABLE_BINDINGS"} *}

theorem COMPOSABLE_BINDINGS_dash [intro] :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS; x \<in> UNDASHED\<rbrakk> \<Longrightarrow> \<langle>b1\<rangle>\<^sub>b (dash x) = \<langle>b2\<rangle>\<^sub>b x"
apply (simp add: COMPOSABLE_BINDINGS_def)
done

theorem COMPOSABLE_BINDINGS_ident [intro] :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS; \<not> x \<in> UNDASHED; \<not> x \<in> DASHED\<rbrakk> \<Longrightarrow> \<langle>b1\<rangle>\<^sub>b x = \<langle>b2\<rangle>\<^sub>b x"
apply (simp only: COMPOSABLE_BINDINGS_def)
apply (simp add: NON_REL_VAR_def)
apply (simp add: binding_equiv_def)
done

(*
subsubsection {* Closure Theorems *}

theorem SkipR_closure [closure] :
"II \<in> WF_PREDICATE"
apply (simp add: SkipR_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem SkipRA_closure [closure] :
"II a \<in> WF_PREDICATE"
  by (simp add: SkipRA_def closure)

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
apply (auto intro!: closure)
done

theorem AssignR_closure [closure] :
"v \<in> WF_EXPRESSION \<Longrightarrow>
x :=p\<^bsub>vs\<^esub> v \<in> WF_PREDICATE"
  by (simp add:AssignR_def closure)
*)

subsubsection {* @{term UNREST} theorems *}

theorem UNREST_SkipR [unrest]:
"UNREST (VAR - (UNDASHED \<union> DASHED)) II"
  by (simp add:SkipR_def UNREST_def WF_BINDING_def override_on_def)

theorem UNREST_SkipRA [unrest]:
"UNREST (VAR - vs) (II vs)"
  by (auto intro:closure unrest simp add:SkipRA_def)

theorem UNREST_AssignR [unrest]:
"\<lbrakk> UNREST_EXPR (VAR - vs1) v \<rbrakk> \<Longrightarrow> 
 UNREST (VAR - ({dash x} \<union> (vs1 \<union> vs2))) (x :=p\<^bsub>vs2\<^esub> v)"
  apply (simp add:AssignR_def)
  apply (rule unrest)
  apply (force intro :unrest)
  apply (force intro :unrest)
done

(*
theorem UNREST_AssignR [unrest]:
"\<lbrakk> UNREST_EXPR (VAR - vs) v \<rbrakk> \<Longrightarrow> 
 UNREST (VAR - ({dash x} \<union> vs)) (x :=p\<^bsub>vs\<^esub> v)"
  apply (subgoal_tac "(VAR - insert (dash x) vs) = (VAR - {dash x}) \<inter> (- vs)") 
  apply (simp add:AssignR_def)
  apply (force intro:closure unrest simp add:AssignR_def)
  apply (auto)
done
*)

theorem UNREST_CondR [unrest]: 
  "\<lbrakk>UNREST vs p1; UNREST vs p2; UNREST vs b\<rbrakk> \<Longrightarrow>
   UNREST vs (p1 \<triangleleft> b \<triangleright> p2)"
  by (auto intro:unrest simp add:CondR_def)

subsection {* Validation of Soundness *}

lemma SemiR_algebraic_lemma1 :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
  CompB ((b1 \<oplus>\<^sub>b b2 on DASHED) \<oplus>\<^sub>b (RenameB SS1 b1) on DASHED_TWICE) SS1 =
   b1 \<oplus>\<^sub>b (RenameB SS1 b2) on DASHED_TWICE"
apply (rule Rep_WF_BINDING_intro)
apply (simp add:CompB_rep_eq)
apply (rule ext)
apply (simp add: RenameB_def closure)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
done

lemma SemiR_algebraic_lemma2 :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
 CompB ((b1 \<oplus>\<^sub>b b2 on DASHED) \<oplus>\<^sub>b (RenameB SS1 b1) on DASHED_TWICE) SS2 =
   b2 \<oplus>\<^sub>b (RenameB SS2 b1) on DASHED_TWICE"
apply (rule Rep_WF_BINDING_intro)
apply (simp)
apply (rule ext)
apply (simp add: RenameB_def closure)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: COMPOSABLE_BINDINGS_dash)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
apply (simp add: COMPOSABLE_BINDINGS_ident)
done

theorem SemiR_algebraic :
"\<lbrakk>UNREST DASHED_TWICE p1;
 UNREST DASHED_TWICE p2\<rbrakk> \<Longrightarrow>
 SemiR p1 p2 = (\<exists>p DASHED_TWICE . p1[SS1] \<and>p p2[SS2])"
apply (rule sym)
apply (utp_pred_tac)
apply (simp add: EvalP_def)
apply (simp add: SemiR_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x =
  "RenameB (inv\<^sub>s SS1) (b \<oplus>\<^sub>b b' on DASHED_TWICE) \<oplus>\<^sub>b b on DASHED_TWICE" in exI)
apply (rule_tac x =
  "RenameB (inv\<^sub>s SS2) (b \<oplus>\<^sub>b b' on DASHED_TWICE) \<oplus>\<^sub>b b on DASHED_TWICE" in exI)
apply (safe)
-- {* Subgoal 1.1 *}
apply (simp add: closure)
apply (rule Rep_WF_BINDING_intro)
apply (rule ext)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: RenameB_def)
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps RenameB_def)
-- {* Subgoal 1.2 *}
apply (auto intro: UNREST_binding_override) [1]
-- {* Subgoal 1.3 *}
apply (auto intro: UNREST_binding_override) [1]
-- {* Subgoal 1.3 *}
apply (simp add: RenameB_def closure)
apply (simp add: COMPOSABLE_BINDINGS_def)
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
apply (simp add: RenameB_def closure)
apply (rule_tac x = "RenameB SS1 b1" in exI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (simp add: SemiR_algebraic_lemma1)
apply (auto intro: UNREST_binding_override simp: closure) [1]
-- {* Subgoal 2.2 *}
apply (simp add: SemiR_algebraic_lemma2)
apply (auto intro: UNREST_binding_override simp: closure) [1]
done

lemma UNREST_SemiR:
      "\<lbrakk> UNREST (VAR - vs1) p1; UNREST (VAR - vs2) p2
       ; vs1 \<subseteq> UNDASHED \<union> DASHED; vs2 \<subseteq> UNDASHED \<union> DASHED
       ; vs3 = (VAR - (in vs1 \<union> out vs2)) \<rbrakk> 
       \<Longrightarrow> UNREST vs3 (p1 ; p2)"
  apply (subgoal_tac "UNREST DASHED_TWICE p1") 
  apply (subgoal_tac "UNREST DASHED_TWICE p2")
  apply (simp add:SemiR_algebraic)
  apply (rule UNREST_ExistsP_alt)
  apply (rule UNREST_AndP_alt)
  apply (rule_tac ?vs1.0="VAR - vs1" in UNREST_RenameP_alt)
  apply (blast intro:unrest)
  apply (force)
  apply (rule_tac ?vs1.0="VAR - vs2" in UNREST_RenameP_alt)
  apply (blast intro:unrest)  
  apply (force)
  apply (simp add:inj_on_image_set_diff[OF Rep_VAR_RENAME_inj])
  apply (simp add:SS1_UNDASHED_DASHED_image[simplified])
  apply (simp add:SS2_UNDASHED_DASHED_image[simplified])
  apply (simp add:VAR_def)
  apply (auto)
  apply (metis DASHED_dash_DASHED_TWICE set_mp out_DASHED)
  apply (metis DASHED_dash_DASHED_TWICE Int_iff UNDASHED_dash_DASHED in_vars_def)
  apply (rule_tac ?vs1.0="VAR - vs2" in UNREST_subset)
  apply (auto)
  apply (rule_tac ?vs1.0="VAR - vs1" in UNREST_subset)
  apply (auto)
done

subsubsection {* Evaluation Theorems *}

theorem EvalP_SkipR [eval] :
"\<lbrakk>II\<rbrakk>b \<longleftrightarrow> (\<forall> v \<in> UNDASHED . \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (dash v))"
apply (simp add: EvalP_def)
apply (simp add: SkipR_def)
done

declare CondR_def [eval]

declare SemiR_algebraic [eval]

subsection {* Proof Experiments *}

theorem SemiP_assoc :
"\<lbrakk>UNREST DASHED_TWICE p1;
 UNREST DASHED_TWICE p2;
 UNREST DASHED_TWICE p3\<rbrakk> \<Longrightarrow>
 p1 ; (p2 ; p3) = (p1 ; p2) ; p3"
apply (subgoal_tac "UNREST DASHED_TWICE (p2 ; p3)")
apply (subgoal_tac "UNREST DASHED_TWICE (p1 ; p2)")
apply (utp_pred_tac)
apply (auto)
oops
end
