(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_rel.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Predicates *}

theory utp_alpha_rel
imports utp_alpha_pred utp_alpha_expr
  "../tactics/utp_alpha_tac" 
  "../tactics/utp_alpha_expr_tac"
  "../tactics/utp_rel_tac"
begin

subsection {* Restrictions *}

definition REL_ALPHABET :: "'VALUE ALPHABET set" where
"REL_ALPHABET = {a . \<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED}"

definition HOM_ALPHABET :: "'VALUE ALPHABET set" where
"HOM_ALPHABET = {a . a \<in> REL_ALPHABET \<and> HOM_ALPHA a}"

definition hom_left ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHABET" ("homl") where
"homl a = in\<^sub>\<alpha> a \<union>\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> a"

definition hom_right ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHABET" ("homr") where
"homr a = undash `\<^sub>f out\<^sub>\<alpha> a \<union>\<^sub>f out\<^sub>\<alpha> a"

definition WF_RELATION :: "'VALUE WF_ALPHA_PREDICATE set" where
"WF_RELATION = {p . (\<alpha> p) \<in> REL_ALPHABET}"

typedef (open) 'VALUE WF_RELATION = "WF_RELATION :: 'VALUE WF_ALPHA_PREDICATE set"
  apply (auto simp add:WF_RELATION_def REL_ALPHABET_def)
  apply (metis ClosureA_alphabet bot_least fempty.rep_eq pred_alphabet_def)
done

definition WF_CONDITION :: "'VALUE WF_ALPHA_PREDICATE set" where
"WF_CONDITION = {p . p \<in> WF_RELATION \<and> UNREST DASHED (\<pi> p)}"

subsection {* Operators *}

subsubsection {* Skip *}

lift_definition SkipA :: "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> a. (a, SkipRA \<langle>a\<rangle>\<^sub>f)"
  by (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)

notation SkipA ("II\<alpha>")

subsubsection {* Assignment *}

definition AssignA ::
"'VALUE VAR \<Rightarrow>
 'VALUE ALPHABET \<Rightarrow>
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow>
 'VALUE WF_ALPHA_PREDICATE" where
"a \<in> REL_ALPHABET \<Longrightarrow>
 AssignA x a v \<equiv> Abs_WF_ALPHA_PREDICATE (a, AssignR x \<langle>a\<rangle>\<^sub>f (\<epsilon> v))"

notation AssignA ("_ :=\<^bsub>_ \<^esub>_" [190] 190)

subsubsection {* Conditional *}

text {* Should we impose a constraint on b for it to be a condition? *}

definition CondA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<and>
 b \<in> WF_CONDITION \<and>
 (\<alpha> r1) = (\<alpha> r2) \<and>
 (\<alpha> b) \<subseteq>\<^sub>f (\<alpha> r1) \<longrightarrow>
 CondA r1 b r2 = Abs_WF_ALPHA_PREDICATE (\<alpha> r1, (\<pi> r1) \<triangleleft> (\<pi> b) \<triangleright> (\<pi> r2))"

notation CondA ("_ \<triangleleft>\<alpha> _ \<alpha>\<triangleright> _")

subsubsection {* Sequential Composition *}

definition SemiA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<longrightarrow>
 SemiA r1 r2 = Abs_WF_ALPHA_PREDICATE (in\<^sub>\<alpha> (\<alpha> r1) \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> r2), (\<pi> r1) ; (\<pi> r2))"

notation SemiA (infixr ";\<alpha>" 140)

subsection {* Theorems *}

theorem WF_RELATION_unfold :
"r \<in> WF_RELATION \<longleftrightarrow>
 \<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
apply (simp add: WF_RELATION_def)
apply (simp add: REL_ALPHABET_def)
done

(*
theorem WF_CONDITION_unfold :
"r \<in> WF_CONDITION \<longleftrightarrow>
 \<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> UNDASHED"
apply (simp add: WF_CONDITION_def WF_RELATION_def REL_ALPHABET_def)
apply (insert WF_ALPHA_PREDICATE_UNREST[of r])
apply (auto)
done
*)

theorem WF_RELATION_intro [intro] :
  "\<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow>
   r \<in> WF_RELATION"
  by (simp add:WF_RELATION_unfold assms)

theorem WF_CONDITION_WF_RELATION [closure] :
"r \<in> WF_CONDITION \<Longrightarrow> r \<in> WF_RELATION"
apply (simp add: WF_CONDITION_def)
done

theorem HOM_ALPHABET_REL_ALPHABET [closure] :
"a \<in> HOM_ALPHABET \<Longrightarrow> a \<in> REL_ALPHABET"
apply (simp add: HOM_ALPHABET_def)
done

theorem WF_RELATION_REL_ALPHABET [closure] :
"r \<in> WF_RELATION \<Longrightarrow> (\<alpha> r) \<in> REL_ALPHABET"
  by (simp add: WF_RELATION_def)

theorem WF_RELATION_UNDASHED_DASHED [closure]:
"r \<in> WF_RELATION \<Longrightarrow> \<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
apply (simp add: WF_RELATION_def)
apply (simp add: REL_ALPHABET_def)
done

theorem WF_RELATION_UNREST_UNDASHED [unrest]:
  "r \<in> WF_RELATION \<Longrightarrow> UNREST DASHED_TWICE (\<pi> r)"
  apply (simp add:WF_RELATION_def REL_ALPHABET_def)
  apply (rule_tac ?vs1.0="VAR - \<langle>\<alpha> r\<rangle>\<^sub>f" in UNREST_subset)
  apply (auto intro:unrest)
done

subsubsection {* Closure Theorems *}

text {* TODO: Provide a complete set of closure theorems! *}

theorem REL_ALPHABET_empty [closure]:
  "\<lbrace>\<rbrace> \<in> REL_ALPHABET"
  by (simp add:REL_ALPHABET_def)

theorem REL_ALPHABET_union [closure]:
  "\<lbrakk> a1 \<in> REL_ALPHABET; a2 \<in> REL_ALPHABET \<rbrakk> \<Longrightarrow> (a1 \<union>\<^sub>f a2) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def)

theorem REL_ALPHABET_inter [closure]:
  "\<lbrakk> a1 \<in> REL_ALPHABET; a2 \<in> REL_ALPHABET \<rbrakk> \<Longrightarrow> (a1 \<inter>\<^sub>f a2) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def)

theorem REL_ALPHABET_minus [closure]:
  "a1 \<in> REL_ALPHABET \<Longrightarrow> (a1 -\<^sub>f a2) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def)

theorem NotA_WF_RELATION [closure] :
"\<lbrakk>r \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 \<not>\<alpha> r \<in> WF_RELATION"
  by (simp add: WF_RELATION_unfold alphabet)

theorem NotA_WF_CONDITION [closure] :
"\<lbrakk>r \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 \<not>\<alpha> r \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:closure)
apply (simp add:NotA.rep_eq)
apply (auto intro: unrest)
done

theorem AndA_WF_RELATION [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 \<and>\<alpha> r2 \<in> WF_RELATION"
  by (simp add: WF_RELATION_unfold alphabet)

theorem AndA_WF_CONDITION [closure] :
"\<lbrakk>r1 \<in> WF_CONDITION;
 r2 \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 r1 \<and>\<alpha> r2 \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:AndA.rep_eq closure)
apply (auto intro:unrest)
done

theorem OrA_WF_RELATION [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 \<or>\<alpha> r2 \<in> WF_RELATION"
  by (simp add: WF_RELATION_unfold alphabet)

theorem OrA_WF_CONDITION [closure] :
"\<lbrakk>r1 \<in> WF_CONDITION;
 r2 \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 r1 \<or>\<alpha> r2 \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:OrA.rep_eq closure)
apply (auto intro:unrest)
done

theorem ImpliesA_WF_RELATION [closure] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 \<Rightarrow>\<alpha> r2 \<in> WF_RELATION"
  by (simp add: WF_RELATION_unfold alphabet)

theorem ImpliesA_WF_CONDITION [closure] :
"\<lbrakk>r1 \<in> WF_CONDITION;
 r2 \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
 r1 \<Rightarrow>\<alpha> r2 \<in> WF_CONDITION"
apply (simp add:WF_CONDITION_def)
apply (simp add:ImpliesA.rep_eq closure)
apply (auto intro:unrest)
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
apply (simp add:TrueA_rep_eq closure)
apply (auto intro:unrest)
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
apply (simp add:FalseA_rep_eq closure)
apply (auto intro:unrest)
done

theorem SkipA_closure [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 II\<alpha> a \<in> WF_RELATION"
  by (simp add: WF_RELATION_def REL_ALPHABET_def pred_alphabet_def SkipA.rep_eq)

theorem AssignA_rep_eq:
  "\<lbrakk> a \<in> REL_ALPHABET; x \<in>\<^sub>f a; dash x \<in>\<^sub>f a; \<alpha> v \<subseteq>\<^sub>f a \<rbrakk> \<Longrightarrow> 
   Rep_WF_ALPHA_PREDICATE (x :=\<^bsub>a\<^esub> v) = (a, AssignR x \<langle>a\<rangle>\<^sub>f (\<epsilon> v))"
  apply (subgoal_tac "(a, x :=p\<^bsub>\<langle>a\<rangle>\<^sub>f \<^esub>\<epsilon> v) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:AssignA_def)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (subgoal_tac "UNREST (VAR - ({dash x} \<union> \<langle>a\<rangle>\<^sub>f)) (x :=p\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub>\<epsilon> v)")
  apply (subgoal_tac "\<langle>a\<rangle>\<^sub>f = {dash x} \<union> (\<langle>a\<rangle>\<^sub>f - {dash x})")
  apply (force)
  apply (force)
  apply (rule UNREST_AssignR)
  apply (metis Diff_mono UNREST_EXPR_subset WF_ALPHA_EXPRESSION_UNREST_EXPR order_refl)
done

theorem AssignA_closure [closure] :
  assumes 
   "a \<in> REL_ALPHABET"
   "x \<in>\<^sub>f a" "dash x \<in>\<^sub>f a"
   "x \<in> UNDASHED"
   "\<alpha> v \<subseteq>\<^sub>f a"
  shows "x :=\<^bsub>a\<^esub> v \<in> WF_RELATION"
proof
  from assms show "\<langle>\<alpha> (x :=\<^bsub>a \<^esub>v)\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
    apply (simp add:AssignA_rep_eq pred_alphabet_def)
    apply (simp add:REL_ALPHABET_def)
  done
qed

theorem RenameA_SS_closure [closure]:
  "p \<in> WF_RELATION \<Longrightarrow> p[SS]\<alpha> \<in> WF_RELATION"
  apply (auto simp add:WF_RELATION_def REL_ALPHABET_def alphabet)
  apply (metis (lifting) SS_VAR_RENAME_INV SS_ident_app UnE VAR_RENAME_INV_app set_rev_mp)
done

theorem CondA_rep_eq :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 (\<alpha> r1) = (\<alpha> r2);
 (\<alpha> b) \<subseteq>\<^sub>f (\<alpha> r1)\<rbrakk> \<Longrightarrow>
  Rep_WF_ALPHA_PREDICATE (r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2) = (\<alpha> r1, (\<pi> r1) \<triangleleft> (\<pi> b) \<triangleright> (\<pi> r2))"
  apply (subgoal_tac "(\<alpha> r1, (\<pi> r1) \<triangleleft> (\<pi> b) \<triangleright> (\<pi> r2)) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:CondA_def)
  apply (simp add: WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest)
done

theorem CondA_closure [closure] :
  assumes "r1 \<in> WF_RELATION" "r2 \<in> WF_RELATION"
    "b \<in> WF_CONDITION" "(\<alpha> r1) = (\<alpha> r2)" "(\<alpha> b) \<subseteq>\<^sub>f (\<alpha> r1)"
 shows "(r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2) \<in> WF_RELATION"
proof 
  from assms show "\<langle>\<alpha> r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
    by (simp add: CondA_rep_eq pred_alphabet_def WF_RELATION_def REL_ALPHABET_def)
qed

theorem SemiA_rep_eq:
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 Rep_WF_ALPHA_PREDICATE (r1 ;\<alpha> r2) = (in\<^sub>\<alpha> (\<alpha> r1) \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> r2), (\<pi> r1) ; (\<pi> r2))"
  apply (subgoal_tac "(in\<^sub>\<alpha> (\<alpha> r1) \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> r2), (\<pi> r1) ; (\<pi> r2)) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:SemiA_def)
  apply (frule WF_RELATION_UNREST_UNDASHED)
  apply (frule WF_RELATION_UNREST_UNDASHED) back
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule UNREST_SemiR)
  apply (auto)
  apply (metis (no_types) UnE WF_RELATION_unfold set_rev_mp)
  apply (metis (hide_lams, no_types) Un_iff WF_RELATION_UNDASHED_DASHED set_rev_mp)
done

theorem SemiA_closure [closure] :
  assumes "r1 \<in> WF_RELATION" "r2 \<in> WF_RELATION"
  shows "r1 ;\<alpha> r2 \<in> WF_RELATION"
apply (simp add: WF_RELATION_unfold pred_alphabet_def)
apply (simp add: SemiA_rep_eq assms)
apply (metis in_vars_def inf_sup_ord(2) le_supI1 le_supI2 out_vars_def)
done

subsection {* Alphabet Theorems *}

declare pred_alphabet_def [simp]

theorem SkipA_alphabet [alphabet] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 \<alpha> (II\<alpha> a) = a"
  by (simp add: SkipA.rep_eq)

theorem AssignA_alphabet [alphabet] :
"\<lbrakk> a \<in> REL_ALPHABET; x \<in>\<^sub>f a; dash x \<in>\<^sub>f a; \<alpha> v \<subseteq>\<^sub>f a \<rbrakk> \<Longrightarrow>
 \<alpha> (x :=\<^bsub>a\<^esub> v) = a"
  by (simp add: AssignA_rep_eq)

theorem CondA_alphabet [alphabet] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 (\<alpha> r1) = (\<alpha> r2);
 (\<alpha> b) \<subseteq>\<^sub>f (\<alpha> r1)\<rbrakk> \<Longrightarrow>
 \<alpha> (r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2) = (\<alpha> r1)"
  by (simp add: CondA_rep_eq)

theorem SemiA_alphabet [alphabet] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 \<alpha> (r1 ;\<alpha> r2) = in\<^sub>\<alpha> (\<alpha> r1) \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> r2)"
  by (simp add: SemiA_rep_eq)

subsection {* Evaluation Theorems *}

theorem EvalP_SkipP_override :
"vs \<subseteq> NON_REL_VAR \<Longrightarrow>
 \<lbrakk>II\<rbrakk>(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>II\<rbrakk>b1"
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
-- {* Subgoal 3 *}
apply (subgoal_tac "v \<notin> vs", simp)
apply (subgoal_tac "dash v \<notin> vs", simp)
apply (auto simp: NON_REL_VAR_def) [1]
apply (auto simp: NON_REL_VAR_def) [1]
done

theorem EvalA_SkipA [evala] :
"a \<in> REL_ALPHABET \<Longrightarrow> \<lbrakk>II\<alpha> a\<rbrakk>\<pi> = II \<langle>a\<rangle>\<^sub>f"
  by (simp add:EvalA_def SkipA.rep_eq)

theorem EvalA_CondA [evala] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 (\<alpha> r1) = (\<alpha> r2);
 (\<alpha> b) \<subseteq>\<^sub>f (\<alpha> r1)\<rbrakk> \<Longrightarrow>
 \<lbrakk>r1 \<triangleleft>\<alpha> b \<alpha>\<triangleright> r2\<rbrakk>\<pi> = \<lbrakk>r1\<rbrakk>\<pi> \<triangleleft> \<lbrakk>b\<rbrakk>\<pi> \<triangleright> \<lbrakk>r2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: CondA_rep_eq)
done

theorem EvalA_SemiA [evala] :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 \<lbrakk>r1 ;\<alpha> r2\<rbrakk>\<pi> = \<lbrakk>r1\<rbrakk>\<pi> ; \<lbrakk>r2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: SemiA_rep_eq)
done

declare pred_alphabet_def [simp del]

subsubsection {* Proof Experiments *}

theorem SemiA_assoc :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 (r1 ;\<alpha> r2) ;\<alpha> r3 = r1 ;\<alpha> (r2 ;\<alpha> r3)"
apply (utp_alpha_tac2)
apply (utp_rel_tac)
apply (auto)
done

theorem SemiA_OrA_distl :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 r1 ;\<alpha> (r2 \<or>\<alpha> r3) = (r1 ;\<alpha> r2) \<or>\<alpha> (r1 ;\<alpha> r3)"
apply (utp_alpha_tac2)
apply (utp_rel_auto_tac)
done

theorem SemiA_OrA_distr :
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 (r1 \<or>\<alpha> r2) ;\<alpha> r3 = (r1 ;\<alpha> r3) \<or>\<alpha> (r2 ;\<alpha> r3)"
apply (utp_alpha_tac2)
apply (utp_rel_auto_tac)
done

theorem SemiA_SkipA_left:
  assumes "r \<in> WF_RELATION" "a \<in> HOM_ALPHABET" "out\<^sub>\<alpha> a = dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> r)"
  shows "II\<alpha> a ;\<alpha> r = r"
proof -

  from assms have ina:"in \<langle>a\<rangle>\<^sub>f = in \<langle>\<alpha> r\<rangle>\<^sub>f"
    by (force elim!:Rep_fset_elim intro!:Rep_fset_intro simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def HOM_ALPHA_unfold)

  moreover with assms(1) have "in\<^sub>\<alpha> a \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> r) = \<alpha> r"
    by (auto simp add:WF_RELATION_def REL_ALPHABET_def in_out_union)

  moreover from assms have "II \<langle>a\<rangle>\<^sub>f ; (\<pi> r) = (\<pi> r)"
  proof -
    have "undash ` (DASHED - dash ` in \<langle>\<alpha> r\<rangle>\<^sub>f) = UNDASHED - in \<langle>\<alpha> r\<rangle>\<^sub>f"
    proof -  
      have "dash ` in \<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> DASHED"
        by (metis out_dash utp_var.out_DASHED)

      thus ?thesis
        by (simp add: inj_on_image_set_diff[OF undash_inj_on_DASHED])
    qed

    with assms show ?thesis
      apply (simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def)
      apply (rule_tac SemiP_SkipRA_left)
      apply (simp_all add:ina)
      apply (insert WF_ALPHA_PREDICATE_UNREST[of r])
      apply (force intro:unrest simp add:closure var_defs)
      apply (force intro:unrest simp add:closure var_defs)
      apply (force intro: assms(1) unrest)
    done
  qed

  ultimately show ?thesis using assms
    by (utp_alpha_tac, simp add: EvalA_def)
qed

theorem SemiA_SkipA_right:
  assumes "r \<in> WF_RELATION" "a \<in> HOM_ALPHABET" "in\<^sub>\<alpha> a = undash `\<^sub>f out\<^sub>\<alpha> (\<alpha> r)"
  shows "r ;\<alpha> II\<alpha> a = r"
proof -
  from assms have ina:"out \<langle>a\<rangle>\<^sub>f = out \<langle>\<alpha> r\<rangle>\<^sub>f"
    by (force elim!:Rep_fset_elim intro!:Rep_fset_intro simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def HOM_ALPHA_unfold)
    
  moreover with assms(1) have alpha:"in\<^sub>\<alpha> (\<alpha> r) \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> r) = \<alpha> r"
    by (auto simp add:WF_RELATION_def REL_ALPHABET_def in_out_union)

  moreover from assms have "(\<pi> r) ; II \<langle>a\<rangle>\<^sub>f = (\<pi> r)"
  proof -
    have "dash ` (UNDASHED - undash ` out \<langle>\<alpha> r\<rangle>\<^sub>f) = DASHED - out \<langle>\<alpha> r\<rangle>\<^sub>f"
      by (simp add: inj_on_image_set_diff[OF dash_inj] dash_UNDASHED_image dash_undash_image out_DASHED)

    with assms show ?thesis
      apply (simp add:WF_RELATION_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def)
      apply (rule_tac SemiP_SkipRA_right)
      apply (simp_all add:closure ina)
      apply (force elim!:Rep_fset_elim intro:UNREST_subset simp add:closure var_defs)
      apply (force elim!:Rep_fset_elim intro:UNREST_subset simp add:closure var_defs)
      apply (force intro: assms(1) unrest)
    done
  qed

  ultimately show ?thesis using assms
    apply (utp_alpha_tac)
    apply (simp add:EvalA_def)
    apply (metis Rep_fset_intro alpha out_alphabet.rep_eq)
  done
qed

theorem ClosureA_rel_closure [closure] :
  "[p]\<alpha> \<in> WF_RELATION"
  apply (simp add:WF_RELATION_def REL_ALPHABET_def)
  apply (simp add:alphabet closure)
done

theorem VarA_rel_closure [closure] :
"x \<in> UNDASHED \<union> DASHED \<Longrightarrow>
VarA x \<in> WF_RELATION"
apply (simp add:WF_RELATION_def REL_ALPHABET_def)
apply (simp add:alphabet closure)
done

lemma SS1_alpha_image: "a \<in> REL_ALPHABET \<Longrightarrow> \<langle>SS1\<rangle>\<^sub>s `\<^sub>f a = (in\<^sub>\<alpha> a) \<union>\<^sub>f dash `\<^sub>f (out\<^sub>\<alpha> a)"
  apply (simp add:REL_ALPHABET_def)
  apply (clarify)
  apply (simp)
  apply (drule SS1_UNDASHED_DASHED_image)
  apply (simp)
done

lemma SS2_alpha_image: "a \<in> REL_ALPHABET \<Longrightarrow> \<langle>SS2\<rangle>\<^sub>s `\<^sub>f a = (dash `\<^sub>f dash `\<^sub>f (in\<^sub>\<alpha> a)) \<union>\<^sub>f (out\<^sub>\<alpha> a)"
  apply (simp add:REL_ALPHABET_def)
  apply (clarify)
  apply (simp)
  apply (drule SS2_UNDASHED_DASHED_image)
  apply (simp)
done

lemma SS_alpha_image: "a \<in> REL_ALPHABET \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s `\<^sub>f a = dash `\<^sub>f (in\<^sub>\<alpha> a) \<union>\<^sub>f undash `\<^sub>f (out\<^sub>\<alpha> a)"
  apply (simp add:REL_ALPHABET_def)
  apply (clarify)
  apply (simp)
  apply (drule SS_UNDASHED_DASHED_image)
  apply (simp)
done


theorem SemiA_algebraic:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION"
  shows "p ;\<alpha> q = (\<exists>-\<alpha> dash `\<^sub>f out\<^sub>\<alpha>(\<alpha> p) \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha>(\<alpha> q). p[SS1]\<alpha> \<and>\<alpha> q[SS2]\<alpha>)"
proof -

  from assms have "\<alpha> (p ;\<alpha> q) = \<alpha> (\<exists>-\<alpha> dash `\<^sub>f out\<^sub>\<alpha>(\<alpha> p) \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha>(\<alpha> q). p[SS1]\<alpha> \<and>\<alpha> q[SS2]\<alpha>)"
    apply (simp add:alphabet SS1_alpha_image SS2_alpha_image closure)
    apply (clarsimp)
    apply (auto simp add:var_simps var_dist var_member var_contra)
    apply (metis (lifting) DASHED_dash_elim not_dash_dash_member_out set_rev_mp utp_var.out_DASHED)
  done

  moreover
  have "\<lbrakk>p ;\<alpha> q\<rbrakk>\<pi> = \<lbrakk>(\<exists>-\<alpha> dash `\<^sub>f out\<^sub>\<alpha>(\<alpha> p) \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha>(\<alpha> q). p[SS1]\<alpha> \<and>\<alpha> q[SS2]\<alpha>)\<rbrakk>\<pi>"
  proof -

    from assms have "\<lbrakk>p ;\<alpha> q\<rbrakk>\<pi> = \<pi> p ; \<pi> q"
      apply (utp_alpha_tac)
      apply (simp add:EvalA_def)
    done

    also from assms have "... = (\<exists>p DASHED_TWICE . (\<pi> p)[SS1] \<and>p (\<pi> q)[SS2])"
      by (simp add: SemiR_algebraic unrest)



    also from assms have "... = (\<exists>p (DASHED_TWICE - dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f)
                              . \<exists>p (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f). (\<pi> p[SS1] \<and>p \<pi> q[SS2]))"
    proof -
      have " (DASHED_TWICE - dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f) \<union> (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f) 
           = DASHED_TWICE"
        by (auto simp add:var_defs)

      thus ?thesis
        by (metis (no_types) ExistsP_union)
    qed

    also from assms have "... = (\<exists>p (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f) . \<pi> p[SS1] \<and>p \<pi> q[SS2])"
    proof -
      from assms have "UNREST (DASHED_TWICE - (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f)) (\<pi> p[SS1] \<and>p \<pi> q[SS2])"
        apply (rule_tac unrest)
        apply (rule_tac unrest)
        apply (rule WF_ALPHA_PREDICATE_UNREST)
        apply (simp add:rename_dist rename_simps SS1_UNDASHED_DASHED_image[simplified] closure)
        apply (auto)
        apply (rule_tac unrest)
        apply (rule WF_ALPHA_PREDICATE_UNREST)
        apply (simp add:rename_dist rename_simps SS2_UNDASHED_DASHED_image[simplified] closure)
        apply (auto)[1]
        apply (metis DASHED_not_DASHED_TWICE in_mono utp_var.out_DASHED)
      done

      thus ?thesis
        apply (rule_tac ExistsP_ident)
        apply (auto intro:unrest)
      done
    qed

    ultimately show ?thesis
      by (utp_alpha_tac, simp add:EvalA_def)
  qed

  ultimately show ?thesis
    by (rule EvalA_intro)

qed

theorem SkipA_unfold :
  assumes "a \<in> REL_ALPHABET" "x \<in> \<langle>a\<rangle>\<^sub>f" "dash x \<in> \<langle>a\<rangle>\<^sub>f" "x \<in> UNDASHED" "HOM_ALPHA a"
  shows "II\<alpha> a = (VarAE (dash x) ==\<alpha> VarAE x) \<and>\<alpha> II\<alpha> (a -\<^sub>f \<lbrace>x,dash x\<rbrace>)"
  apply (insert assms)
  apply (utp_alpha_tac2)
  apply (simp add:HOM_ALPHA_HOMOGENEOUS)
  apply (simp add:SkipRA_unfold)
done
end