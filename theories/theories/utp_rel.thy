(******************************************************************************)
(* Title: utp/theories/utp_rel.thy                                            *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Relational Predicates *}

theory utp_rel
imports "../generic/utp_generic"
begin

context GEN_PRED
begin

subsection {* Restrictions *}

definition WF_RELATION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_RELATION =
 {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p \<subseteq> UNDASHED \<union> DASHED}"

definition WF_CONDITION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_CONDITION =
 {p . p \<in> WF_RELATION \<and> p = (\<exists>p DASHED . p)}"

subsection {* Substitutions *}

definition SS1 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS1 v = (
 if dashes (name v) = 1 then (dash v) else
 if dashes (name v) = 2 then (undash v) else v)"

definition SS2 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS2 v = (
 if dashes (name v) = 0 then dash (dash v) else
 if dashes (name v) = 2 then undash (undash v) else v)"

subsection {* Relational Operators *}

definition CondR ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ \<triangleleft> _ \<triangleright> _") where
"p1 \<in> WF_RELATION \<and>
 p2 \<in> WF_RELATION \<and>
 b \<in> WF_CONDITION \<and>
 \<alpha> p1 = \<alpha> p2 \<and>
 \<alpha> b \<subseteq> \<alpha> p1 \<longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) = (b \<and>p p1) \<or>p (\<not>p b \<and>p p2)"

definition SemiR ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" (infixr ";" 140) where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<and>
 COMPOSABLE (\<alpha> r1) (\<alpha> r2) \<longrightarrow>
 r1 ; r2 = (\<exists>-p dash ` (out (\<alpha> r1)) . r1[SS1] \<and>p r2[SS2])"

text {* Configure theorems for the predicate proof tactic. *}

declare CondR_def [eval]
declare SemiR_def [eval]

subsection {* Theorems *}

subsubsection {* Restrictions *}

theorem WF_RELATION_WF_ALPHA_PREDICATE :
"p \<in> WF_RELATION \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_RELATION_def)
done

declare WF_RELATION_WF_ALPHA_PREDICATE [eval]

subsubsection {* Substitutions *}

theorem SS1_VAR_SUBST [simp] :
"SS1 \<in> VAR_SUBST"
apply (simp add: SS1_def_raw)
apply (simp add: VAR_SUBST_def)
apply (simp_all add: dash_def undash_def)
apply (rule bijI)
apply (rule injI)
sorry

theorem SS2_VAR_SUBST [simp] :
"SS2 \<in> VAR_SUBST"
apply (simp add: SS2_def_raw)
apply (simp add: VAR_SUBST_def)
apply (simp_all add: dash_def undash_def)
apply (rule bijI)
apply (rule injI)
sorry

subsubsection {* Alphabet Theorems *}

theorem CondR_alphabet [simp]:
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<triangleleft> b \<triangleright> p2) = \<alpha> p1"
apply (simp add: CondR_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
apply (auto)
done

theorem SemiR_alphabet [simp] :
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<and>
 COMPOSABLE (\<alpha> r1) (\<alpha> r2) \<longrightarrow>
 \<alpha> (r1 ; r2) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
apply (simp add: SemiR_def)
apply (simp add: WF_RELATION_def)
apply (simp add: WF_ALPHABET_alphabet)
apply (safe)
-- {* Subgoal 1 *}
apply (case_tac "xa \<in> DASHED")
apply (simp add: SS1_def DASHED_def)
apply (simp add: out_alphabet_def DASHED_def)
apply (subgoal_tac "xa \<in> UNDASHED")
apply (simp add: SS1_def in_alphabet_def UNDASHED_def)
apply (auto)
-- {* Subgoal 2 *}
sorry

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

subsubsection {* Closure Theorems *}

theorem CondR_closure [simp] :
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) \<in> WF_RELATION"
apply (simp add: CondR_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
done

theorem SemiR_closure [simp] :
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<and>
 COMPOSABLE (\<alpha> r1) (\<alpha> r2) \<longrightarrow>
 r1 ; r2 \<in> WF_RELATION"
apply (simp add: SemiR_def)
apply (simp add: WF_RELATION_def)
apply (simp add: WF_ALPHABET_alphabet)
apply (auto)
-- {* Subgoal 1 *}
apply (case_tac "xa \<in> DASHED")
apply (simp add: SS1_def DASHED_def)
apply (simp add: out_alphabet_def DASHED_def)
apply (subgoal_tac "xa \<in> UNDASHED")
apply (simp add: SS1_def UNDASHED_def)
apply (auto)
-- {* Subgoal 2 *}
apply (case_tac "xa \<in> UNDASHED")
apply (simp add: WF_ALPHABET_alphabet COMPOSABLE_def)
apply (simp add: SS2_def UNDASHED_def)
apply (simp add: in_alphabet_def UNDASHED_def)
apply (subgoal_tac "xa \<in> DASHED")
apply (simp add: SS2_def DASHED_def)
apply (auto)
done

theorem WF_RELATION_TrueP [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 a \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 true a \<in> WF_RELATION"
apply (simp only: WF_RELATION_def)
apply (auto)
done

theorem WF_RELATION_FalseP [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 a \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 false a \<in> WF_RELATION"
apply (simp only: WF_RELATION_def)
apply (auto)
done

subsection {* Proof Experiments *}

theorem
"\<lbrakk>r \<in> WF_RELATION;
 a \<in> WF_ALPHABET;
 a \<subseteq> UNDASHED \<union> DASHED;
 COMPOSABLE a (\<alpha> r)\<rbrakk> \<Longrightarrow>
 false a ; r = false ((in a) \<union> out (\<alpha> r))"
apply (utp_pred_eq_tac)
apply (auto)
-- {* TODO: See if the proof of the subgoals can be automated. *}
oops
end
end
