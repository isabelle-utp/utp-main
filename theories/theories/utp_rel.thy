(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/theories/utp_rel.thy                                             *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* Relational Predicates *}

theory utp_rel
imports "../generic/utp_generic" "../generic/utp_expression" Relation
begin

type_synonym ('VALUE, 'TYPE) ASSIGN = "('TYPE VAR * ('VALUE, 'TYPE) ALPHA_EXPRESSION)"
type_synonym ('VALUE, 'TYPE) ASSIGNMENT = "('VALUE,'TYPE) ASSIGN list"

definition assign_var :: "('VALUE, 'TYPE) ASSIGN \<Rightarrow> 'TYPE VAR" where
"assign_var \<equiv> fst"

definition assign_value :: "('VALUE, 'TYPE) ASSIGN \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"assign_value \<equiv> snd"


context GEN_EXPR
begin

subsection {* Restrictions *}

definition WF_RELATION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_RELATION =
 {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p \<subseteq> UNDASHED \<union> DASHED}"

definition WF_CONDITION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_CONDITION =
 {p . p \<in> WF_RELATION \<and> p = (\<exists>p DASHED . p)}"

subsection {* Renamings *}

definition SS_conv :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS_conv v = (if v \<in> DASHED then undash v else
              if v \<in> UNDASHED then dash v else v)"

definition SS1 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS1 v = (
 if (v \<in> DASHED) then (dash v) else
 if (v \<in> DASHED_TWICE) then (undash v) else v)"

definition SS2 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS2 v = (
 if dashes (name v) = 0 then dash (dash v) else
 if dashes (name v) = 2 then undash (undash v) else v)"

definition SS3 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS3 v = (
 if dashes (name v) = 0 then dash (dash (dash v)) else
 if dashes (name v) = 3 then undash (undash (undash v)) else v)"

definition SS4 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS4 v = (
 if dashes (name v) = 1 then dash (dash v) else
 if dashes (name v) = 3 then undash (undash v) else v)"

subsection {* Relational Operators *}
      
definition SkipR ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<Pi>_") where
"a \<in> WF_ALPHABET \<longrightarrow>
 \<Pi> a = LiftP (homalph a) (\<lambda> b . \<forall> x \<in> in (homalph a) . b x = b (dash x))"

definition ConvR ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_\<^sup>\<smile>") where
"r \<in> WF_RELATION \<longrightarrow> r\<^sup>\<smile> = r[SS_conv]"

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

definition SemiB :: "('VALUE, 'TYPE) ALPHA_PREDICATE
                    \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE
                    \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" (infixr ";\<^sub>B" 140) where
"p \<in> WF_RELATION \<and> q \<in> WF_RELATION \<and>
 COMPOSABLE (\<alpha> p) (\<alpha> q) \<longrightarrow>
  SemiB p q = ((in (\<alpha> p)) \<union> (out (\<alpha> q))
             ,{(b \<oplus> b1 on in (\<alpha> p)) \<oplus> b2 on out (\<alpha> q) 
              | b1 b2 b. b1 \<in> \<beta> p \<and> b2 \<in> \<beta> q \<and> b \<in> WF_BINDING
                     \<and> (\<forall>x \<in> in(\<alpha> q). b1 (dash x) = b2 x) })"

definition IterR :: "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ * _") where
"p \<in> WF_RELATION \<and>
 b \<in> WF_CONDITION \<and>
 \<alpha> b \<subseteq> \<alpha> p \<longrightarrow> IterR b p = (\<mu> (\<alpha> p) (\<lambda> x. (p ; x) \<triangleleft> b \<triangleright> \<Pi> (\<alpha> p)))"

definition AssignR :: 
"'TYPE VAR \<Rightarrow> 'TYPE ALPHABET \<Rightarrow> 
 ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ :=\<^bsub>_ \<^esub>_") where
"x \<in> UNDASHED \<and> x \<in> a \<and> dash x \<in> a \<and> 
 a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<union> DASHED \<longrightarrow> AssignR x a e = (dash x =p e) \<and>p (\<Pi> (a - {x, dash x}))"

(*
inductive WF_ASSIGNMENT :: "'TYPE ALPHABET \<Rightarrow> (('VALUE, 'TYPE) ASSIGNMENT) \<Rightarrow> bool" 
where
"WF_ASSIGNMENT a []" | 
"\<lbrakk> dash (assign_var v) \<in> a
 ; expr_type (assign_value v) = var_type (assign_var v)
 ; assign_var v \<in> UNDASHED
 ; assign_value v \<in> WF_ALPHA_EXPR
 ; \<alpha>e (assign_value v) \<subseteq> a
 ; \<alpha>e (assign_value v) \<subseteq> UNDASHED
 ; WF_ASSIGNMENT (a - {dash (assign_var v)}) vs \<rbrakk> 
 \<Longrightarrow> WF_ASSIGNMENT a (v # vs)"

inductive_cases WF_ASSIGNMENT_cons' [elim!]: "WF_ASSIGNMENT a (v # vs)"

thm WF_ASSIGNMENT_cons'

(*
lemma WF_ASSIGNMENT_cons[elim!]:
"\<lbrakk>WF_ASSIGNMENT a (v # vs);
 \<lbrakk>dash (assign_var v) \<in> a; expr_type (assign_value v) = type (assign_var v); assign_var v \<in> UNDASHED;
  assign_value v \<in> WF_ALPHA_EXPR; \<alpha>e (assign_value v) \<subseteq> a; \<alpha>e (assign_value v) \<subseteq> UNDASHED; WF_ASSIGNMENT (a - {dash (assign_var v)}) vs\<rbrakk>
 \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P"
  by auto
*)

primrec mkAssign :: "('VALUE, 'TYPE) ASSIGNMENT \<Rightarrow> 'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"mkAssign [] a = \<Pi> a" |
"mkAssign (v # vs) a = ((dash (assign_var v) =p assign_value v) \<and>p mkAssign vs (a - {dash (assign_var v)}))"

definition AssignR :: "('VALUE, 'TYPE) ASSIGNMENT \<Rightarrow> 'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"WF_ASSIGNMENT a xs \<and> a \<in> WF_ALPHABET 
 \<and> a \<subseteq> UNDASHED \<union> DASHED \<and> HOMOGENEOUS a \<longrightarrow> 
 AssignR xs a = mkAssign xs a"

abbreviation AssignR_1 :: "'TYPE VAR \<Rightarrow> 'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ :=\<^bsub>_ \<^esub>_") where
"AssignR_1 x a e \<equiv> AssignR [(x,e)] a"
*)

(* ("_ :=\<^bsub>_ \<^esub>_") *)

text {* Configure theorems for the automatic proof tactic. *}

declare SkipR_def [eval]
declare CondR_def [eval]
declare SemiR_def [eval]
declare AssignR_def [eval]

lemma SemiR_eval[eval]: 
"\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; COMPOSABLE (\<alpha> p) (\<alpha> q) \<rbrakk>
 \<Longrightarrow> EvalP (p ; q) b = (EvalP (\<exists>-p dash ` (out (\<alpha> p)) . (p[SS1] \<and>p q[SS2])) b)"
  by (simp add:SemiR_def)

subsection {* Theorems *}

subsubsection {* Restrictions *}

theorem WF_RELATION_WF_ALPHA_PREDICATE :
"p \<in> WF_RELATION \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_RELATION_def)
done

theorem WF_CONDITION_WF_ALPHA_PREDICATE :
"p \<in> WF_CONDITION \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_CONDITION_def WF_RELATION_def closure)
done

theorem WF_RELATION_alphabet [alphabet] :
"p \<in> WF_RELATION \<Longrightarrow> \<alpha> p \<in> WF_ALPHABET"
apply (auto simp add: WF_RELATION_def)
done

declare WF_RELATION_alphabet [eval]

theorem WF_RELATION_UNDASHED_DASHED :
"p \<in> WF_RELATION \<Longrightarrow> \<alpha> p \<subseteq> UNDASHED \<union> DASHED"
  by (simp add: WF_RELATION_def)

subsubsection {* Renamings *}

text {* Simon's Theorems *}

theorem SS1_total : "x \<in> range SS1"
apply(auto simp add:SS1_def image_def dash_def undash_def DASHED_TWICE_def DASHED_def)
apply(metis (hide_lams, mono_tags) NAME.simps(1) NAME.surjective SIMPLE_NAME.simps(1) SIMPLE_NAME.simps(2) fst_conv numeral_2_eq_2 pairI snd_conv unit.exhaust)
done

theorem SS2_total : "x \<in> range SS2"
apply (case_tac x, case_tac a)
apply (auto simp add:SS2_def image_def dash_def undash_def)
apply (smt NAME.simps(1) SIMPLE_NAME.simps(1) SIMPLE_NAME.simps(2) fst_conv snd_conv)
done

theorem SS3_total : "x \<in> range SS3"
apply (case_tac x, case_tac a)
apply (auto simp add:SS3_def image_def dash_def undash_def DASHED_def UNDASHED_def)
apply (smt MkVar_def NAME.simps(1) One_nat_def SIMPLE_NAME.simps(1) SIMPLE_NAME.simps(2) Suc_pred' VarE_type fst_conv snd_conv)
done

theorem SS_conv_total : "x \<in> range SS_conv"
apply (case_tac x, case_tac a)
apply (auto simp add:SS_conv_def image_def dash_def undash_def DASHED_def UNDASHED_def)
apply (metis NAME.simps(1) SIMPLE_NAME.simps(1) SIMPLE_NAME.simps(2) fst_conv not_less_eq snd_eqD)
done

theorem SS1_VAR_RENAME [simp, intro] :
"SS1 \<in> VAR_RENAME"
apply(simp only:VAR_RENAME_ON_def)
apply(auto simp add:bij_def inj_on_def SS1_def DASHED_TWICE_def DASHED_def)
apply (auto simp add : SS1_def
  bij_def inj_on_def undash_def dash_def)
apply (smt NAME.equality prod_eq_iff unit.exhaust)+
apply (rule SS1_total)
done

theorem SS2_VAR_RENAME [simp, intro] :
"SS2 \<in> VAR_RENAME"
apply(simp only:VAR_RENAME_ON_def)
apply (auto simp add : SS2_def
  bij_def inj_on_def undash_def dash_def)
apply (smt NAME.equality prod_eq_iff unit.exhaust)+
apply (rule SS2_total)
done

theorem SS3_VAR_RENAME [simp, intro] :
"SS3 \<in> VAR_RENAME"
apply(simp only:VAR_RENAME_ON_def)
apply (auto simp add : SS3_def
  bij_def inj_on_def undash_def dash_def)
apply (smt NAME.equality prod_eq_iff unit.exhaust)+
apply (rule SS3_total)
done

lemma SS_conv_VAR_RENAME [simp] : "SS_conv \<in> VAR_RENAME"
apply(simp only:VAR_RENAME_ON_def)
apply (auto simp add: SS_conv_def undash_def dash_def bij_def inj_on_def DASHED_def UNDASHED_def)
apply (smt NAME.equality prod_eq_iff unit.exhaust)+
apply (rule SS_conv_total)
done

theorem SS1_dashes [simp, intro, eval] :
"a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> SS1 ` a = in a \<union> dash ` (out a)"
apply (force simp add: SS1_def DASHED_def UNDASHED_def DASHED_TWICE_def
  Un_def in_alphabet_def out_alphabet_def image_def SS1_def)
done

theorem SS1_invol[simp]:
"SS1 \<circ> SS1 = id"
apply(auto simp add: comp_def SS1_def id_def var)
apply(rule ext)
apply(auto simp add:var)
apply(case_tac "dashes(name x) = 0")
apply(auto simp add:var undash_def dash_def DASHED_def DASHED_TWICE_def)

apply(metis (full_types) NAME.surjective numeral_2_eq_2 pair_collapse unit.exhaust)+
done

theorem SS2_dashes[simp, intro, eval] :
"a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> SS2 ` a = (dash ` dash ` in a) \<union> (out a)"
apply (auto simp add: SS2_def DASHED_def UNDASHED_def
  Un_def in_alphabet_def out_alphabet_def)
apply (simp_all add:image_def SS2_def)
apply (rule bexI, auto)+
done

theorem SS2_invol[simp]:
"SS2 \<circ> SS2 = id"
apply(auto simp add: SS2_def id_def comp_def)
apply(rule ext)
apply(case_tac "dashes(name x) = 0")
apply(auto)
apply(auto simp add:undash_def dash_def intro:NAME.equality NAME.surjective unit.exhaust pairI)
apply(case_tac x)
apply(case_tac a)
apply(auto)
apply(smt NAME.surjective pairI unit.exhaust)
done

lemma SS_conv_invol[simp]:
  "SS_conv \<circ> SS_conv = id"
apply(auto simp add: SS_conv_def id_def comp_def)
apply(rule ext)
apply(auto simp add:DASHED_def UNDASHED_def dash_def undash_def)
apply (metis (full_types) NAME.surjective pairI unit.exhaust)+
done

theorem RenameB_SS1_beta_equiv[simp]:
"\<lbrakk> b1 \<in> WF_BINDING; b2 \<in> WF_BINDING; a \<subseteq> UNDASHED \<rbrakk> \<Longrightarrow> 
  (RenameB SS1 b1 \<cong> b2 on a) = (b1 \<cong> b2 on a)" 
  sorry
(*
  apply(auto simp add: RenameB_def UNDASHED_def beta_equiv_def)
  apply(erule_tac x="x" in ballE)
  apply(subgoal_tac "dashes (name x) = 0")
  apply(auto simp add:var closure binding)
  apply (smt SS1_VAR_RENAME SS1_def VAR_RENAME_inv_ss)
  apply(erule_tac x="x" in ballE)
  apply(subgoal_tac "dashes (name x) = 0")
  apply(auto)
  apply(smt SS1_VAR_RENAME SS1_def VAR_RENAME_inv_ss)
done  
*)

theorem RenameB_SS2_beta_equiv[simp]:
"\<lbrakk> b1 \<in> WF_BINDING; b2 \<in> WF_BINDING; a \<subseteq> DASHED \<rbrakk> \<Longrightarrow> 
  (RenameB SS2 b1 \<cong> b2 on a) = (b1 \<cong> b2 on a)" 
  apply(auto simp add: RenameB_def DASHED_def beta_equiv_def)
  apply(erule_tac x="x" in ballE)
  apply(subgoal_tac "dashes (name x) = 1")
  apply(auto)
  apply (smt SS2_VAR_RENAME SS2_def VAR_RENAME_inv_ss)
  apply(erule_tac x="x" in ballE)
  apply(subgoal_tac "dashes (name x) = 1")
  apply(auto)
  apply(smt SS2_VAR_RENAME SS2_def VAR_RENAME_inv_ss)
done  

theorem SS1_d0: "x \<in> UNDASHED \<Longrightarrow> SS1 x = x"
  by (simp add:SS1_def var UNDASHED_def DASHED_TWICE_def DASHED_def)

theorem SS1_d1: "x \<in> DASHED \<Longrightarrow> SS1 x = dash x"
  by (simp add:SS1_def var UNDASHED_def DASHED_TWICE_def DASHED_def)

theorem SS1_d2: "x \<in> DASHED_TWICE \<Longrightarrow> SS1 x = undash x"
  by (simp add:SS1_def var UNDASHED_def DASHED_TWICE_def DASHED_def)

theorem SS2_d0: "x \<in> UNDASHED \<Longrightarrow> SS2 x = dash (dash x)"
  by (simp add:SS2_def var UNDASHED_def DASHED_TWICE_def DASHED_def)

theorem SS2_d1: "x \<in> DASHED \<Longrightarrow> SS2 x = x"

  by (simp add:SS2_def DASHED_def)

theorem SS2_d2: "x \<in> DASHED_TWICE \<Longrightarrow> SS2 x = undash (undash x)"
  by (simp add:SS2_def DASHED_TWICE_def)

theorem SS1_undashed: "a \<subseteq> UNDASHED \<Longrightarrow> SS1 ` a \<subseteq> UNDASHED"
  by (smt SS1_d0 image_subsetI subsetD)

theorem SS1_dashed: "a \<subseteq> DASHED \<Longrightarrow> SS1 ` a \<subseteq> DASHED_TWICE"
  apply(rule_tac image_subsetI)
  apply(drule subsetD)
  apply(auto simp add:SS1_d1 DASHED_TWICE_def DASHED_def dash_def)
done

theorem SS1_inv_d2[simp]:
"x \<in> DASHED_TWICE \<Longrightarrow> inv SS1 x = undash x"
apply(subgoal_tac "x \<in> -UNDASHED")
apply(simp add:inv_def)
apply(rule some_equality)
apply(simp add:SS1_def)
apply(simp add:DASHED_TWICE_def dash_def undash_def DASHED_def UNDASHED_def var)
sorry

(*
apply(simp add:SS1_def)
apply(auto)
apply(auto simp add:DASHED_TWICE_def UNDASHED_def undash_def)
done

*)

theorem SS2_inv_d2[simp]:
"x \<in> DASHED_TWICE \<Longrightarrow> inv SS2 x = undash (undash x)"
apply(simp add:inv_def)
apply(rule some_equality)
apply(subgoal_tac "undash (undash x) \<in> UNDASHED")
apply(subgoal_tac "undash x \<in> -UNDASHED")
apply(simp add:SS2_def)
apply(auto simp add:UNDASHED_def DASHED_def DASHED_TWICE_def undash_def dash_def)
apply (metis (full_types) NAME.surjective numeral_2_eq_2 pair_collapse unit.exhaust)
apply(auto simp add:SS2_def undash_def dash_def)
apply(metis (full_types) NAME.surjective pairI unit.exhaust)
done

lemma SS1_beta_equiv_in:
assumes "p \<in> WF_ALPHA_PREDICATE" "bp \<in> \<beta> p" "a \<subseteq> in (\<alpha> p)"
shows "RenameB SS1 bp \<cong> bp on a"
  by (smt RenameB_SS1_beta_equiv in_undashed WF_BINDING_predicate assms beta_equiv_def beta_equiv_subset)

lemma SS1_override_in:
assumes "p \<in> WF_ALPHA_PREDICATE" "bp \<in> \<beta> p" "a \<subseteq> in (\<alpha> p)"
shows "RenameB SS1 bp \<oplus> bp on a = RenameB SS1 bp"
  by (metis SS1_beta_equiv_in assms beta_equiv_override)

(* Unfortunately I have to specialise this, as the First Order ATPs don't seem
   to cope with subset proofs very well (even trivial ones) *)
lemma SS1_override_in':
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; bp \<in> \<beta> p \<rbrakk> \<Longrightarrow>
   RenameB SS1 bp \<oplus> bp on in (\<alpha> p) = RenameB SS1 bp"
  by (auto intro: SS1_override_in)

lemma SS2_beta_equiv_out:
assumes "p \<in> WF_ALPHA_PREDICATE" "bp \<in> \<beta> p" "a \<subseteq> out (\<alpha> p)"
shows "RenameB SS2 bp \<cong> bp on a"
  by (smt RenameB_SS2_beta_equiv out_undashed WF_BINDING_predicate assms beta_equiv_def beta_equiv_subset)

lemma SS2_override_out:
assumes "p \<in> WF_ALPHA_PREDICATE" "bp \<in> \<beta> p" "a \<subseteq> out (\<alpha> p)"
shows "RenameB SS2 bp \<oplus> bp on a = RenameB SS2 bp"
  by (metis SS2_beta_equiv_out assms beta_equiv_override)

lemma SS2_override_out':
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; bp \<in> \<beta> p  \<rbrakk> \<Longrightarrow>
   RenameB SS2 bp \<oplus> bp on out (\<alpha> p) = RenameB SS2 bp"
  by (auto intro: SS2_override_out)

lemma SS1_SS2_overlap:
assumes "p \<in> WF_ALPHA_PREDICATE" "q \<in> WF_ALPHA_PREDICATE" "bp \<in> \<beta> p" "bq \<in> \<beta> q"
        "\<forall>x\<in>in (\<alpha> q). bp (dash x) = bq x" 
shows "RenameB SS1 bp \<cong> RenameB SS2 bq on (dash ` dash ` in (\<alpha> q))"
proof -
  from assms have "bp \<in> WF_BINDING" "bq \<in> WF_BINDING"
    by (auto simp add:WF_ALPHA_PREDICATE_def WF_BINDING_SET_def)    

  with assms show ?thesis
    by (simp add:beta_equiv_def RenameB_def) 
       (metis SS1_inv_d2 SS2_inv_d2 VAR.in_undashed dash_dashed dash_undashed imageI subsetD undash_dash)
qed

lemma SS1_SS2_alpha_union1:
"\<lbrakk> a \<in> WF_ALPHABET; b \<in> WF_ALPHABET ; COMPOSABLE a b
 ; a \<subseteq> UNDASHED \<union> DASHED; b \<subseteq> UNDASHED \<union> DASHED \<rbrakk> \<Longrightarrow> 
  SS1 ` a \<union> SS2 ` b = SS1 ` a \<union> out b"
  by auto

lemma SS1_SS2_alpha_union2:
"\<lbrakk> a \<in> WF_ALPHABET; b \<in> WF_ALPHABET ; COMPOSABLE a b
 ; a \<subseteq> UNDASHED \<union> DASHED; b \<subseteq> UNDASHED \<union> DASHED \<rbrakk> \<Longrightarrow> 
  SS1 ` a \<union> SS2 ` b = in a \<union> SS2 ` b"
  by auto

lemma SS1_RenameB:
  "b \<in> WF_BINDING \<Longrightarrow> RenameB SS1 (RenameB SS1 b) = b"
  by (metis SS1_VAR_RENAME SS1_invol RenameB_invol)

lemma SS2_RenameB:
  "b \<in> WF_BINDING \<Longrightarrow> RenameB SS2 (RenameB SS2 b) = b"
  by (metis SS2_VAR_RENAME SS2_invol RenameB_invol)

lemma SS1_image_invol:
  "SS1 ` SS1 ` a = a"
  by (metis SS1_invol image_compose o_id undash_dash')

lemma SS2_image_invol:
  "SS2 ` SS2 ` a = a"
  by (metis SS1_image_invol SS1_invol SS2_invol image_compose)

subsubsection {* Alphabet Theorems *}

theorem WF_BINDING_FUN_SkipR [simplified,simp] :
"(\<lambda> b . \<forall> x \<in> in (homalph a) . f (b x) (b (dash x))) \<in> WF_BINDING_FUN (homalph a)"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: beta_equiv_def)
apply(subgoal_tac "\<forall>x\<in>in (homalph a).x \<in> homalph a")
apply(subgoal_tac "\<forall>x\<in>in (homalph a).dash x \<in> homalph a")
apply(auto)
apply(auto simp add:homalph_def)
apply (metis (lifting) Un_iff VAR.dash_undash_out VAR.homalph_in homalph_def image_eqI)
apply (metis (lifting) UnE homalph_def homalph_in)
done

theorem SkipR_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS a \<rbrakk> \<Longrightarrow>
 \<alpha> (\<Pi> a) = a"
apply (simp add: SkipR_def alpha_closure alphabet closure binding var)
sorry

theorem CondR_alphabet [alphabet]:
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<triangleleft> b \<triangleright> p2) = \<alpha> p1"
  apply(simp add:CondR_def)
  apply(simp only:WF_CONDITION_def WF_RELATION_def CondR_def)
  apply(auto simp add: CondR_def alphabet closure alpha_closure)
done

theorem SemiR_alphabet [alphabet] :
assumes assm:
  "r1 \<in> WF_RELATION"
  "r2 \<in> WF_RELATION"
  "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
shows "\<alpha> (r1 ; r2) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
  by (insert assm, auto simp add: SemiR_def alphabet WF_RELATION_def closure alpha_closure var)

lemma SemiR_in_alpha: "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; COMPOSABLE (\<alpha> p) (\<alpha> q) \<rbrakk> \<Longrightarrow> in (\<alpha> (p ; q)) = in (\<alpha> p)"
  by (simp add:alphabet alpha_closure closure var)

lemma SemiR_out_alpha: "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; COMPOSABLE (\<alpha> p) (\<alpha> q) \<rbrakk> \<Longrightarrow> out (\<alpha> (p ; q)) = out (\<alpha> q)"
  by (simp add:alphabet alpha_closure closure var)

theorem SemiB_alphabet [alphabet] :
assumes assm:
  "r1 \<in> WF_RELATION"
  "r2 \<in> WF_RELATION"
  "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
shows "\<alpha> (r1 ;\<^sub>B r2) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
  apply(insert assms)
  apply(simp add:SemiB_def)
done

subsubsection {* Closure Theorems *}

theorem SkipR_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
  a \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 (\<Pi> a) \<in> WF_RELATION"
apply (simp add:SkipR_def WF_RELATION_def)
apply (auto simp add: closure alphabet alpha_closure binding var)
sorry

theorem ConvR_closure [closure] :
"\<lbrakk>r \<in> WF_RELATION\<rbrakk> \<Longrightarrow> r\<^sup>\<smile> \<in> WF_RELATION"
apply(simp add:ConvR_def WF_RELATION_def)
apply(auto simp add:SS_conv_def DASHED_def UNDASHED_def dash_def undash_def closure alphabet)
done

theorem CondR_closure [closure] :
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) \<in> WF_RELATION"
apply (simp add: CondR_def WF_RELATION_def WF_CONDITION_def)
apply (simp add: alphabet closure)
done

theorem SemiR_closure [closure]:
assumes assm:
  "r1 \<in> WF_RELATION"
  "r2 \<in> WF_RELATION"
  "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
shows "r1 ; r2 \<in> WF_RELATION"
proof -
  from assm have "r1 ; r2 \<in> WF_ALPHA_PREDICATE"
    by (simp add:alphabet alpha_closure closure eval WF_RELATION_def)

  with assm show ?thesis
    by (simp add:WF_RELATION_def, auto simp add: in_alphabet_def out_alphabet_def closure alphabet)
qed

lemma SemiB_wfalpha[alphabet]: "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; COMPOSABLE (\<alpha> p) (\<alpha> q) \<rbrakk> \<Longrightarrow>
                      \<alpha> (SemiB p q) \<in> WF_ALPHABET"
  by (simp add:SemiB_def closure alphabet alpha_closure)

lemma SemiB_closure[closure]: 
assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "COMPOSABLE (\<alpha> p) (\<alpha> q)"
shows "SemiB p q \<in> WF_RELATION"
proof -
  from assms have "\<alpha> (p ;\<^sub>B q) \<in> WF_ALPHABET"
    by (auto simp add:alphabet closure alpha_closure)

  also from assms have "\<beta> (p ;\<^sub>B q) \<in> WF_BINDING_SET (\<alpha> (p ;\<^sub>B q))"
    apply(simp add:WF_BINDING_SET_def SemiB_def)
    apply(auto)
    apply(metis WF_BINDING_override WF_BINDING_predicate WF_RELATION_WF_ALPHA_PREDICATE)
    apply(smt VAR.override_out_in beta_equiv_comm beta_equiv_override beta_equiv_override_3 beta_equiv_trans beta_equiv_union)
  done

  moreover from assms have "\<alpha> (p ;\<^sub>B q) \<subseteq> UNDASHED \<union> DASHED"
    by (auto simp add:SemiB_def in_alphabet_def out_alphabet_def)
   
  ultimately show ?thesis
    by (auto simp only:WF_RELATION_def WF_ALPHA_PREDICATE_def)

qed

(*
lemma mkAssign_closure[closure]:
"\<lbrakk> WF_ASSIGNMENT a vs; a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<union> DASHED \<rbrakk>
   \<Longrightarrow> mkAssign vs a \<in> WF_RELATION"
proof (induct vs arbitrary: a)
  case Nil
  thus ?case 
    by (simp add:alphabet closure)

next
  case (Cons v vs)

  moreover from `v # vs \<in> WF_ASSIGNMENT a` have "vs \<in> WF_ASSIGNMENT (a - {dash (assign_var v)})"
    by auto

  moreover from `a \<in> WF_ALPHABET` have alp:"a - {dash (assign_var v)} \<in> WF_ALPHABET"
    by (simp add:WF_ALPHABET_def)

  moreover from `a \<subseteq> UNDASHED \<union> DASHED` have ud:"a - {dash (assign_var v)} \<subseteq> UNDASHED \<union> DASHED"
    by auto

  moreover from calculation have "mkAssign vs (a - {dash (assign_var v)}) \<in> WF_RELATION"
    by simp

  moreover from calculation have "assign_value v \<in> WF_ALPHA_EXPR" "assign_var v \<in> UNDASHED"
    by auto

  moreover from calculation have "\<alpha>e (VarE (dash (assign_var v))) \<subseteq> UNDASHED \<union> DASHED"
    apply(safe)
    apply(simp add:VarE_def)
    apply(subgoal_tac "assign_var v \<in> UNDASHED")
    apply(simp add:dash_def UNDASHED_def DASHED_def)
    apply(simp)
  done

  moreover from calculation have "\<alpha>e (assign_value v) \<subseteq> UNDASHED \<union> DASHED"
    by force
        
  moreover from calculation have "VarE (dash (assign_var v)) =p assign_value v \<in> WF_RELATION"
    by (simp add:WF_RELATION_def)

  ultimately show ?case
    by (simp add:WF_RELATION_def)
qed

lemma AssignR_closure[simp]:
"\<lbrakk> vs \<in> WF_ASSIGNMENT a; a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS a \<rbrakk>
   \<Longrightarrow> AssignR vs a \<in> WF_RELATION"
  by (simp add:AssignR_def)

theorem mkAssign_alphabet [simp] :
"\<lbrakk> vs \<in> WF_ASSIGNMENT a; a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<union> DASHED \<rbrakk> \<Longrightarrow>
 \<alpha> (mkAssign vs a) = homalph a"
proof (induct vs arbitrary: a)
  fix a
  case Nil
    thus ?case
      by (simp add:SkipR_def)
next        

  case (Cons v vs)

  moreover from calculation have "assign_value v \<in> WF_ALPHA_EXPR"
    by (auto)

  moreover from calculation have "a - {assign_var v} \<in> WF_ALPHABET" "vs \<in> WF_ASSIGNMENT (a - {dash (assign_var v)})" "a - {dash (assign_var v)} \<subseteq> UNDASHED \<union> DASHED"
    by auto

  moreover from calculation have "mkAssign vs (a - {dash (assign_var v)}) \<in> WF_RELATION"
    by simp

  moreover from calculation have "\<alpha> (mkAssign (v # vs) a) = \<alpha> (VarE (dash (assign_var v)) =p assign_value v) \<union> \<alpha> (mkAssign vs (a - {dash (assign_var v)}))"

    apply(simp)

      apply(subgoal_tac "(VarE (dash (assign_var v)) =p assign_value v) \<in> WF_ALPHA_PREDICATE")
      apply(subgoal_tac "mkAssign vs (a - {dash (assign_var v)}) \<in> WF_ALPHA_PREDICATE")
      apply(simp add:AndP_def)
      apply(insert calculation)
      apply(simp only:WF_RELATION_def)
      apply(simp)
      apply(simp)
  done

  moreover from calculation have "\<alpha> (VarE (dash (assign_var v)) =p assign_value v) = {dash (assign_var v)}\<union>\<alpha>e (assign_value v)"
    by simp

  moreover from calculation have "\<alpha> (VarE (dash (assign_var v)) =p assign_value v) \<subseteq> a"
    by auto

  moreover from calculation have "\<alpha> (mkAssign vs (a - {dash (assign_var v)})) = homalph (a - {dash (assign_var v)})"
    by auto


  moreover from calculation have "a \<subseteq> homalph a"
    by (metis homalpha_subset)

  moreover from calculation have "dash (assign_var v) \<in> homalph a"
    by (smt Un_insert_left insert_subset subset_trans)

  moreover from calculation have "\<alpha>e (assign_value v) \<subseteq> homalph a"
    apply(subgoal_tac "\<alpha>e (assign_value v) \<subseteq> a")
    apply(metis subset_trans)
    apply(auto)
  done

  moreover from calculation have "\<alpha> (mkAssign (v # vs) a) \<subseteq> homalph a"
    apply(simp)
    apply(rule homalpha_mono)
    apply(force)
  done
    
  moreover from calculation have "homalph a \<subseteq> \<alpha> (mkAssign (v # vs) a)"
    proof -
      have r0:"dash (assign_var v) \<in> out (homalph a)"
        by (metis Un_iff in_alphabet_ndash calculation(15) homalph_def homalph_in homalph_out)

      with calculation have r1:"homalph a = in (homalph a) \<union> (out (homalph a) - {dash (assign_var v)}) \<union> {dash (assign_var v)}"
      proof -
        have "homalph a = in (homalph a) \<union> out (homalph a)"
          by (metis homalpha_dashes in_out_complete)
        also from r0 have "... = in (homalph a) \<union> (out (homalph a) - {dash (assign_var v)}) \<union> {dash (assign_var v)}"
          by (force)
        ultimately show ?thesis 
          by metis
      qed

      have r2:"in (homalph a) \<subseteq> homalph (a - {dash (assign_var v)})"
        apply(simp add:homalph_def)
        apply(auto)
        apply (metis DiffI IntE IntI image_empty image_insert in_alphabet_def in_dash)
        sorry

      have r3: "out (homalph a) - {dash (assign_var v)} \<subseteq> homalph (a - {dash (assign_var v)})"
        apply(simp add:homalph_def)
        apply(auto)
        apply (metis VAR.out_undash_out equals0D)
        apply (metis DiffI IntE IntI emptyE insertE out_alphabet_def)
        sorry

      have r4: "{dash (assign_var v)} \<subseteq> {dash (assign_var v)}"
        by simp
      
      have r5: "(in (homalph a) \<union> (out (homalph a) - {dash (assign_var v)}) \<union> {dash (assign_var v)}) \<subseteq> ({dash (assign_var v)} \<union> \<alpha>e (assign_value v) \<union> homalph (a - {dash (assign_var v)}))"
        by (smt Un_least Un_upper1 Un_upper2 r2 r3 subset_trans)


      thus ?thesis
        by (simp only:calculation, metis r1)
        
    qed

  ultimately show ?case
    by force
qed      

theorem AssignR_alphabet [simp] :
"\<lbrakk> vs \<in> WF_ASSIGNMENT a; a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS a \<rbrakk> \<Longrightarrow>
 \<alpha> (AssignR vs a) = a"
  by (simp add:AssignR_def homogeneous_homalpha)
*)


theorem WF_RELATION_TrueP [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 a \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 true a \<in> WF_RELATION"
apply (simp only: WF_RELATION_def) 
apply (auto simp add:closure alphabet)
done

theorem WF_RELATION_FalseP [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 a \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 false a \<in> WF_RELATION"
apply (simp only: WF_RELATION_def)
apply (auto simp add:closure alphabet)
done

subsection {* Proof Experiments *}

(* Convert this into a decent set of lemmas in the right place *)
lemma dashed_twice_override:
"\<lbrakk> p \<in> WF_RELATION; bq \<in> WF_BINDING; bp \<in> \<beta> p; a \<subseteq> DASHED_TWICE \<rbrakk> \<Longrightarrow>
 bp \<oplus> bq on a \<in> \<beta> p"
  apply(auto simp add:WF_RELATION_def)
  apply(subgoal_tac "bp \<cong> (bp \<oplus> bq on a) on \<alpha> p")
  apply(subgoal_tac "bp \<oplus> bq on a \<in> WF_BINDING")
  apply(auto intro:beta_equiv_bindings)
apply (metis WF_BINDING_override WF_BINDING_predicate)
apply(subgoal_tac "\<alpha> p \<inter> a = {}")
apply (metis Int_commute beta_equiv_comm beta_equiv_override_2)
apply(simp add:DASHED_def UNDASHED_def DASHED_TWICE_def Un_def)
sorry

(*
apply (smt Collect_def disjoint_iff_not_equal in_mono mem_def)
done
*)

declare COMPOSABLE_def [alphabet]

lemma EqualityR_intro[intro!]: "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; \<alpha> p = \<alpha> q; \<forall>b\<in>WF_BINDING. EvalP p b = EvalP q b \<rbrakk> \<Longrightarrow> p = q"
  apply (case_tac p)
  apply (case_tac q)
  apply (auto simp add: WF_RELATION_def WF_ALPHA_PREDICATE_def EvalP_def WF_BINDING_SET_def)
done

lemma stern: "\<lbrakk> \<alpha> p \<subseteq> UNDASHED \<union> DASHED; p \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow> p \<in> WF_RELATION"
  by (simp add:WF_RELATION_def)


(*
lemma SemiR_assoc:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
          "COMPOSABLE (\<alpha> p) (\<alpha> q)" "COMPOSABLE (\<alpha> q) (\<alpha> r)" 
  shows "p ; (q ; r) = (p ; q) ; r"
apply(insert assms)
apply(rule EqualityR_intro)
apply(force intro!:closure simp add: alphabet alpha_rules)
apply(force intro!:closure simp add: alphabet alpha_rules)
apply(simp add:alphabet alpha_rules closure)
apply(auto simp add:WF_RELATION_def)
apply(simp add:eval alphabet closure alpha_rules binding stern)
apply(subgoal_tac "\<alpha> (\<exists>-p dash ` dash ` in (\<alpha> q) . p[SS1] \<and>p q[SS2]) \<subseteq> UNDASHED \<union> DASHED")
apply(subgoal_tac "COMPOSABLE (\<alpha> (\<exists>-p dash ` dash ` in (\<alpha> q) . p[SS1] \<and>p q[SS2])) (\<alpha> r)")

apply(simp add:eval alphabet alpha_rules closure stern RenameB_def)

apply(auto)
*)

(*

(* Show that the two versions of sequential composition are equal *)
theorem SemiR_SemiB:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "COMPOSABLE (\<alpha> p) (\<alpha> q)"
  shows "p ; q = p ;\<^sub>B q"
proof
  (* First we show that the two alphabets are equal *)
  from assms have salpha: "\<alpha> (p ; q) = in (\<alpha> p) \<union> out (\<alpha> q)"
    by (simp add:alphabet)

  from assms show "\<alpha> (p ; q) = \<alpha> (p ;\<^sub>B q)"
    by (simp add:SemiB_def alphabet)

  from assms have comp: "dash ` dash ` in (\<alpha> q) = dash ` out (\<alpha> p)"
    by (simp add:COMPOSABLE_def var alphabet)

  from assms have preds: "p \<in> WF_ALPHA_PREDICATE" "q \<in> WF_ALPHA_PREDICATE"
    by (simp_all add:WF_RELATION_def)

  (* We prove equivalence of the bindings by two inequalities *)
  from assms show "bindings (p ; q) = bindings (p ;\<^sub>B q)"
  proof (rule_tac subset_antisym)
    (* \<beta> (p ; q) \<subseteq> \<beta> (p ;\<^sub>B q) *)

   from assms preds salpha show "\<beta> (p ; q) \<subseteq> \<beta> (p ;\<^sub>B q)"
   proof (simp add:SemiB_def SemiR_def ExistsResP_def ResP_def, simp add: AndP_def, simp add: RenameP_def, auto)
     from assms have "dash ` out (\<alpha> p) \<in> WF_ALPHABET"
       by auto

     fix bp bq bx

     assume assms':
       "bp \<in> \<beta> p" "bq \<in> \<beta> q" "bx \<in> WF_BINDING" 
       "RenameB SS2 bq \<cong> bx on in (\<alpha> p) \<union> out (\<alpha> q)"
       "RenameB SS1 bp = RenameB SS2 bq"

     from preds assms' have binds: "bp \<in> WF_BINDING" "bq \<in> WF_BINDING"
       by (auto simp add:WF_ALPHA_PREDICATE_def WF_BINDING_SET_def)

     have adashes: "in (\<alpha> p) \<subseteq> UNDASHED" "out (\<alpha> q) \<subseteq> DASHED"
       by (auto simp add:in_alphabet_def out_alphabet_def)

     from assms' binds adashes have bxbp: "bx \<cong> bp on in (\<alpha> p)"
       by (metis RenameB_SS1_beta_equiv beta_equiv_comm beta_equiv_union)

     from assms' binds adashes have bxbq: "bx \<cong> bq on out (\<alpha> q)"
       by (metis RenameB_SS2_beta_equiv beta_equiv_comm beta_equiv_union)

     from bxbp bxbq have bxover: "bx = (bx \<oplus> bp on in (\<alpha> p)) \<oplus> bq on out (\<alpha> q)"
       by (metis beta_equiv_override)

     moreover from assms' binds have "\<forall>x\<in>in (\<alpha> q). bp (dash x) = bq x"
     proof (auto simp add:RenameB_def)
       fix x
       assume assms'': "x \<in> in (\<alpha> q)" "bp \<circ> inv SS1 = bq \<circ> inv SS2"
       hence dash2: "dash (dash (x)) \<in> DASHED_TWICE"
         by (simp add:dash_def in_alphabet_def UNDASHED_def DASHED_TWICE_def)

       from assms'' have "bp (inv SS1 (dash (dash x))) = bq (inv SS2 (dash (dash x)))"
         by (simp add:fun_eq_iff)

       with assms'' show "bp (dash x) = bq x"
         by (metis SS1_inv_d2 SS2_inv_d2 dash2 undash_dash)
     qed

     ultimately show "\<exists> b1 b2 b.
                bx = (b \<oplus> b1 on in (\<alpha> p)) \<oplus> b2 on out (\<alpha> q) \<and>
                b1 \<in> \<beta> p \<and>
                b2 \<in> \<beta> q \<and> b \<in> WF_BINDING \<and> (\<forall>x\<in>in (\<alpha> q). b1 (dash x) = b2 x)"
       by (metis assms')
   qed

   (* \<beta> (p ;\<^sub>B q) \<subseteq> \<beta> (p ; q) *)

   from assms preds salpha show "\<beta> (p ;\<^sub>B q) \<subseteq> \<beta> (p ; q)"
   proof (simp add:SemiB_def SemiR_def ExistsResP_def ResP_def, simp add: AndP_def, simp add: RenameP_def, auto)
     fix bp bq bx
     assume assms': "bp \<in> \<beta> p" "bq \<in> \<beta> q" "bx \<in> WF_BINDING" "\<forall>x\<in>in (\<alpha> q). bp (dash x) = bq x"

     from preds assms' have binds: "bp \<in> WF_BINDING" "bq \<in> WF_BINDING"
       by (auto simp add:WF_ALPHA_PREDICATE_def WF_BINDING_SET_def)
     
     with preds show "(bx \<oplus> bp on in (\<alpha> p)) \<oplus> bq on out (\<alpha> q) \<in> WF_BINDING"
       by (metis WF_BINDING_override assms')

    from assms' have "RenameB SS1 bp \<in> RenameB SS1 ` \<beta> p"
      by auto

    have inbp: "(bx \<oplus> RenameB SS1 bp on SS1 ` \<alpha> p) \<oplus> RenameB SS2 bq on SS2 ` \<alpha> q
          \<in> RenameB SS1 ` \<beta> p"
    proof -

      have "(RenameB SS1 bx \<oplus> bp on \<alpha> p) \<oplus> RenameB SS1 bq on SS1 ` out (\<alpha> q) \<in> \<beta> p"
        by (smt SS1_VAR_RENAME SS1_dashed RenameB_closure assms' assms bindings_override binds dashed_twice_override out_undashed override_on_comm preds)
      
      also have " ((bx \<oplus> RenameB SS1 bp on SS1 ` \<alpha> p) \<oplus> RenameB SS2 bq on SS2 ` \<alpha> q)
                = (RenameB SS1 ((RenameB SS1 bx \<oplus> bp on \<alpha> p) \<oplus> RenameB SS1 bq on SS1 ` out (\<alpha> q)))"
        (* Yes this step takes a _long_ time, we could do with resolving this... *)
        by (smt SS1_SS2_alpha_union1 SS1_SS2_overlap SS1_VAR_RENAME SS2_dashes SS2_override_out' RenameB_closure RenameB_invol RenameB_override1 WF_ALPHABET_out WF_BINDING_override WF_RELATION_UNDASHED_DASHED WF_RELATION_alphabet assms' assms beta_equiv_override binds SS1_RenameB override_on_assoc preds)

    ultimately show ?thesis
      by (metis imageI)
  qed

  have inbq:"(bx \<oplus> RenameB SS1 bp on SS1 ` \<alpha> p) \<oplus> RenameB SS2 bq on SS2 ` \<alpha> q \<in> RenameB SS2 ` \<beta> q"
  proof -
    have b1:"(RenameB SS2 bx \<oplus> RenameB SS2 bp on SS2 ` in (\<alpha> p)) \<in> WF_BINDING"
      by (metis SS2_VAR_RENAME RenameB_closure WF_BINDING_override assms'(3) binds(1))

    then have "(RenameB SS2 bx \<oplus> RenameB SS2 bp on SS2 ` in (\<alpha> p)) \<oplus> bq on (\<alpha> q) \<in> \<beta> q"
      by (metis WF_BINDING_override assms'(2) beta_equiv_bindings beta_equiv_override_3 beta_equiv_refl binds(2) preds(2))


    also have " ((bx \<oplus> RenameB SS1 bp on SS1 ` \<alpha> p) \<oplus> RenameB SS2 bq on SS2 ` \<alpha> q)
              = RenameB SS2 ((RenameB SS2 bx \<oplus> RenameB SS2 bp on SS2 ` in (\<alpha> p)) \<oplus> bq on (\<alpha> q))"
      by (smt SS1_SS2_alpha_union2 SS1_override_in' SS2_RenameB SS2_VAR_RENAME RenameB_closure RenameB_override1 WF_ALPHABET_in WF_BINDING_override WF_RELATION_UNDASHED_DASHED WF_RELATION_alphabet assms' assms binds override_on_assoc override_on_cancel6 preds)
    

 
(*
sledgehammer min [z3] (SS1_SS2_alpha_union1 SS1_SS2_alpha_union2 SS1_SS2_overlap SS1_VAR_RENAME SS1_invol SS1_dashes SS1_override_in' SS2_VAR_RENAME SS2_invol SS2_dashes SS2_override_out' SS2_RenameB RenameB_closure RenameB_invol RenameB_override1 RenameB_override2 WF_ALPHABET_image WF_ALPHABET_in WF_ALPHABET_out WF_BINDING_override WF_RELATION_UNDASHED_DASHED WF_RELATION_alphabet assms' assms beta_equiv_override binds image_compose image_id override_on_assoc override_on_comm preds out_undashed bindings_override override_on_cancel5 override_on_cancel6)

*)

    ultimately show ?thesis
      by (metis imageI)

  qed
      
  from assms assms' have eqt:"(bx \<oplus> RenameB SS1 bp on SS1 ` \<alpha> p) \<oplus> RenameB SS2 bq on SS2 ` \<alpha> q \<cong> (bx \<oplus> bp on in (\<alpha> p)) \<oplus> bq on out (\<alpha> q) on in (\<alpha> p) \<union> out (\<alpha> q)"
    apply(auto intro!:beta_equiv_override_intro1 beta_equiv_override_intro1 [THEN beta_equiv_comm] beta_equiv_refl)
    apply(auto intro:beta_equiv_empty simp add:WF_RELATION_def)
    apply(rule_tac SS1_beta_equiv_in)
    apply(auto)
    apply(rule_tac SS2_beta_equiv_out)
    apply(auto)
  done
    


  from assms' show "\<exists>b1a\<in>RenameB SS1 ` \<beta> p \<inter> RenameB SS2 ` \<beta> q.
    b1a \<cong> (bx \<oplus> bp on in (\<alpha> p)) \<oplus> bq on out (\<alpha> q) on in (\<alpha> p) \<union> out (\<alpha> q)"
    apply(rule_tac x="(bx \<oplus> (RenameB SS1 bp) on (SS1 ` \<alpha> p)) \<oplus> (RenameB SS2 bq) on (SS2 ` \<alpha> q)" in bexI)
    apply(auto simp add:inbp inbq eqt)

  done

  qed
  qed
qed

(* Below is a partial proof sketch for proof of associativity of SemiR without using
   the auxiliary definition. But I don't have the time to prove it now, it would be nice
   to have this finished, because at the very least it should unmask a load of lemmas
   that we need any way.
*)

(*
lemma SemiR_assoc:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
          "COMPOSABLE (\<alpha> p) (\<alpha> q)" "COMPOSABLE (\<alpha> q) (\<alpha> r)" 
  shows "p ; (q ; r) = (p ; q) ; r"
proof -
  have a1:"SS2 ` dash ` out (\<alpha> q) = undash ` (out (\<alpha> q))"
    by (auto simp add:image_def SS2_def undash_def dash_def out_alphabet_def DASHED_def)

  have a2: "SS3 \<in> VAR_RENAME_ON (undash ` (out (\<alpha> q)) \<union> dash ` dash ` (out (\<alpha> q)))"
    sorry

  from assms have "p ; (q ; r) = (\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p (\<exists>-p dash ` (out (\<alpha> q)) . q[SS1] \<and>p r[SS2])[SS2])"
    apply(subgoal_tac "q ; r \<in> WF_RELATION")
    apply(subgoal_tac "COMPOSABLE (\<alpha> p) (\<alpha> (q ; r))")
    apply(simp add:SemiR_def)
    apply(simp add:COMPOSABLE_def)
    apply(metis SemiR_closure)
  done

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p (\<exists>-p SS2 ` dash ` (out (\<alpha> q)) . q[SS1][SS2] \<and>p r[SS2][SS2]))"
    by (metis (no_types) AndP_closure ExistsResP_intrude SS1_VAR_RENAME SS2_VAR_RENAME RenameP_AndP_distr RenameP_closure WF_ALPHABET_image WF_ALPHABET_out WF_RELATION_WF_ALPHA_PREDICATE WF_RELATION_alphabet)

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p (\<exists>-p SS2 ` dash ` (out (\<alpha> q)) . q[SS1][SS2] \<and>p r))"
    by (simp add:WF_RELATION_def, metis RenameP_invol SS2_invol SS2_VAR_RENAME)

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p (\<exists>-p undash ` (out (\<alpha> q)) . q[SS1][SS2] \<and>p r))"
    by (metis a1)

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p (\<exists>-p undash ` (out (\<alpha> q)) \<union> dash ` dash ` (out (\<alpha> q)) . q[SS1][SS2] \<and>p r))"
  proof -
    from assms have "undash ` (out (\<alpha> q)) \<in> WF_ALPHABET"
      by (metis WF_ALPHABET_out WF_ALPHABET_image WF_RELATION_alphabet)

    moreover from assms have "dash ` dash ` (out (\<alpha> q)) \<in> WF_ALPHABET"
      by (metis VAR.WF_ALPHABET_out WF_ALPHABET_image WF_RELATION_alphabet)

    moreover from assms have "dash ` dash ` out (\<alpha> q) \<inter> \<alpha> (q[SS1][SS2] \<and>p r) = {}"
      sorry

    ultimately show ?thesis
      by (metis AndP_closure ExistsResP_merge ExistsResP_vacuous SS1_VAR_RENAME SS2_VAR_RENAME RenameP_closure WF_RELATION_WF_ALPHA_PREDICATE assms)
  qed

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p (\<exists>-p undash ` (out (\<alpha> q)) \<union> dash ` dash ` (out (\<alpha> q)). (q[SS1][SS2] \<and>p r)[id \<oplus> SS3 on undash ` (out (\<alpha> q)) \<union> dash ` dash ` (out (\<alpha> q))]))"
    by (metis AndP_closure ExistsResP_image SS1_VAR_RENAME SS2_VAR_RENAME RenameP_closure VAR.WF_ALPHABET_image VAR.WF_ALPHABET_out WF_ALPHABET_alphabet WF_ALPHABET_union WF_RELATION_WF_ALPHA_PREDICATE a2)    

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p (\<exists>-p dash ` dash ` (out (\<alpha> q)). (q[SS1][SS2] \<and>p r)[id \<oplus> SS3 on undash ` (out (\<alpha> q)) \<union> dash ` dash ` (out (\<alpha> q))]))"
    sorry

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) \<union> dash ` dash ` (out (\<alpha> q)) . p[SS1] \<and>p (q[SS1][SS2] \<and>p r)[id \<oplus> SS3 on undash ` (out (\<alpha> q)) \<union> dash ` dash ` (out (\<alpha> q))])"
    sorry

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> p)) \<union> dash ` dash ` (out (\<alpha> q)) . p[SS1] \<and>p (q[SS1][SS2] \<and>p r)[SS3])"


  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> q)) \<union> dash ` dash ` (out (\<alpha> p)) . (p[SS4] \<and>p q[SS2][SS1][SS4]) \<and>p r[SS2])"

  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> q)) . ((\<exists>-p (out (\<alpha> p)) . p \<and>p q[SS2][SS1]) \<and>p r[SS2]))"


  also from assms have "... = (\<exists>-p dash ` (out (\<alpha> q)) . ((\<exists>-p dash ` (out (\<alpha> p)) . p[SS1] \<and>p q[SS2])[SS1] \<and>p r[SS2]))"
    sledgehammer

qed
*)


lemma SemiB_assoc:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
          "COMPOSABLE (\<alpha> p) (\<alpha> q)" "COMPOSABLE (\<alpha> q) (\<alpha> r)" 
  shows "p ;\<^sub>B (q ;\<^sub>B r) = (p ;\<^sub>B q) ;\<^sub>B r"
proof -
  from assms have alphas1: "\<alpha> p \<in> WF_ALPHABET" "\<alpha> q \<in> WF_ALPHABET" "\<alpha> r \<in> WF_ALPHABET"
    apply(simp_all only:WF_RELATION_def WF_ALPHA_PREDICATE_def)
    apply(auto)
  done

  from assms have alphas2: "\<alpha> (p ;\<^sub>B q) \<in> WF_ALPHABET" "\<alpha> (q ;\<^sub>B r) \<in> WF_ALPHABET"
    by (simp_all add:SemiB_wfalpha)

  from alphas1 alphas2 assms have comps:"COMPOSABLE (\<alpha> p) (\<alpha> (q ;\<^sub>B r))" 
                                        "COMPOSABLE (\<alpha> (p ;\<^sub>B q)) (\<alpha> r)"
    apply(simp_all add:COMPOSABLE_def SemiB_def)
    apply(auto simp add:in_alphabet_def dash_def out_alphabet_def)
  done
   
  from assms have closed: "p ;\<^sub>B q \<in> WF_RELATION" "q ;\<^sub>B r \<in> WF_RELATION"
    by (auto intro:SemiB_closure)
 
  show ?thesis
  proof

    show "\<beta> (p ;\<^sub>B (q ;\<^sub>B r)) = \<beta> ((p ;\<^sub>B q) ;\<^sub>B r)"
    proof
          
      from assms alphas1 comps closed show "\<beta> (p ;\<^sub>B (q ;\<^sub>B r)) \<subseteq> \<beta> ((p ;\<^sub>B q) ;\<^sub>B r)"
        apply(auto simp add:SemiB_def)
        apply(rule_tac x="(b \<oplus> b1 on in (\<alpha> p)) \<oplus> b1a on out (\<alpha> q)" in exI)
        apply(rule_tac x="b2a" in exI)
        apply(rule_tac x="b" in exI)
        apply(auto)
        apply (metis override_on_cancel6 override_out_in)
        apply(rule_tac x="b1" in exI)
        apply(rule_tac x="b1a" in exI)
        apply(rule_tac x="b" in exI)
        apply(auto)
        apply(subgoal_tac "x \<notin> out (\<alpha> r)")
        apply(simp)
        apply(subgoal_tac "in (\<alpha> p) \<inter> out (\<alpha> r) = {}")
        apply (metis (no_types) disjoint_iff_not_equal in_out_disj)
        apply (metis in_out_disj)
      done
          
    next

      from assms alphas1 comps closed show "\<beta> ((p ;\<^sub>B q) ;\<^sub>B r) \<subseteq> \<beta> (p ;\<^sub>B (q ;\<^sub>B r))"
        apply(auto simp add:SemiB_def)
        apply(rule_tac x="b1a" in exI)
        apply(rule_tac x="(b \<oplus> b2a on in (\<alpha> q)) \<oplus> b2 on out (\<alpha> r)" in exI) 
        apply(rule_tac x="b" in exI)
        apply(auto)
        apply (metis override_on_cancel6 override_out_in)
        apply(rule_tac x="b2a" in exI)
        apply(rule_tac x="b2" in exI)
        apply(rule_tac x="b" in exI)
        apply(auto)
        apply(subgoal_tac "x \<notin> out (\<alpha> r)") 
        apply(simp)
        apply (metis IntI equals0D in_out_disj)
      done
    qed
  next

    from assms alphas1 comps closed show "\<alpha> (p ;\<^sub>B q ;\<^sub>B r) = \<alpha> ((p ;\<^sub>B q) ;\<^sub>B r)"
      by (simp add:SemiB_def)

  qed
qed

lemma SemiR_assoc:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
          "COMPOSABLE (\<alpha> p) (\<alpha> q)" "COMPOSABLE (\<alpha> q) (\<alpha> r)" 
  shows "p ; (q ; r) = (p ; q) ; r"
proof -
  from assms have c1:"COMPOSABLE (\<alpha> p) (\<alpha> (q ; r))"
    by (simp add:COMPOSABLE_def)

  from assms have c2:"COMPOSABLE (\<alpha> (p ; q)) (\<alpha> r)"
    apply(simp add:COMPOSABLE_def)
    apply(metis out_alphabet_out)
  done

  have "p ; (q ; r) = p ;\<^sub>B (q ;\<^sub>B r)"
    by (metis SemiR_SemiB SemiR_closure assms c1)

  also have "... = (p ;\<^sub>B q) ;\<^sub>B r"
    by (metis SemiB_assoc assms)

  also have "... = (p ; q) ; r"
    by (metis SemiR_SemiB SemiR_closure assms c2)

  ultimately show ?thesis
    by simp
qed
 
theorem SemiR_left_anhil:
 assumes assm: "r \<in> WF_RELATION" "a \<in> WF_ALPHABET" "a \<subseteq> UNDASHED \<union> DASHED" "COMPOSABLE a (\<alpha> r)"
 shows "false a ; r = false ((in a) \<union> out (\<alpha> r))"
  by (insert assm, utp_pred_eq_tac) (auto simp add:WF_RELATION_def)

theorem SemiR_right_anhil:
 assumes assm: "r \<in> WF_RELATION" "a \<in> WF_ALPHABET" "a \<subseteq> UNDASHED \<union> DASHED" "COMPOSABLE (\<alpha> r) a"
 shows "r ; false a = false ((out a) \<union> in (\<alpha> r))"
  by (insert assm, utp_pred_eq_tac) (auto simp add:WF_RELATION_def)

theorem SemiR_left_ident:
 assumes assm: "r \<in> WF_RELATION" "a \<in> WF_ALPHABET" "a \<subseteq> UNDASHED \<union> DASHED" "HOMOGENEOUS a" "COMPOSABLE a (\<alpha> r)"
 shows "\<Pi> a ; r = r"
proof -
  note assm
  moreover 
  from assm have "(\<Pi> a ; r) \<in> WF_RELATION"
    by (simp)

  moreover
  from assm have "\<alpha> (\<Pi> a ; r) = \<alpha> r"
    apply(simp add:COMPOSABLE_def HOMOGENEOUS_def)
    apply (metis in_out_complete undash_dash' WF_RELATION_UNDASHED_DASHED)
  done

  moreover have "\<beta> (\<Pi> a ; r) = \<beta> r"
  proof
    from assm show "\<beta> (\<Pi> a ; r) \<subseteq> \<beta> r"
    apply(simp add:SemiR_SemiB SemiB_def)
    apply(simp add:SkipR_def LiftP_def)
    apply(auto)
    proof -
      fix b1 b2 b
      assume assm': "b1 \<in> WF_BINDING" "\<forall>x\<in>in a \<union> undash ` out a. b1 x = b1 (dash x)" 
             "b2 \<in> \<beta> r" "b \<in> WF_BINDING" "\<forall>x\<in>in (\<alpha> r). b1 (dash x) = b2 x"

      moreover from assms have "in a = in (\<alpha> r)"
        apply(simp add:HOMOGENEOUS_def COMPOSABLE_def)
        apply(metis undash_dash')
      done
        
      moreover from assms have "\<alpha> r \<subseteq> UNDASHED \<union> DASHED"
        by (simp add:WF_RELATION_def)

      moreover from calculation have "(b \<oplus> b1 on in (\<alpha> r)) \<oplus> b2 on out (\<alpha> r) \<cong> b2 on \<alpha> r"
      proof -
        note calculation
        moreover from calculation have "b1 \<cong> b2 on in (\<alpha> r)"
          by (metis UnI1 beta_equiv_def)

        moreover from calculation have "(b \<oplus> b1 on in (\<alpha> r)) \<oplus> b2 on out (\<alpha> r) = b \<oplus> (b1 \<oplus> b2 on out (\<alpha> r)) on \<alpha> r"
          by (metis in_out_complete override_on_assoc)

        ultimately show "(b \<oplus> b1 on in (\<alpha> r)) \<oplus> b2 on out (\<alpha> r) \<cong> b2 on \<alpha> r"
          by (smt beta_equiv_comm beta_equiv_override beta_equiv_override_3 beta_equiv_refl beta_equiv_union in_out_complete override_out_in)
      qed

      ultimately show "(b \<oplus> b1 on in a) \<oplus> b2 on out (\<alpha> r) \<in> \<beta> r"
        by (smt WF_BINDING_bindings WF_BINDING_override WF_RELATION_WF_ALPHA_PREDICATE beta_equiv_bindings beta_equiv_comm in_mono assm(1))
    qed
  
  next
    from assm show "\<beta> r \<subseteq> \<beta> (\<Pi> a ; r)"
    apply(simp add:SemiR_SemiB SemiB_def)
    apply(simp add:SkipR_def LiftP_def)
    apply(auto)
    proof -
      fix br
      assume br:"br \<in> \<beta> r"

      let ?b  = "br" and
          ?b1 = "\<lambda> x. if (x \<in> in a) then br x else if (x \<in> out a) then br (undash x) else br x" and
          ?b2 = "br"

      note br

      moreover from br have brwf:"br \<in> WF_BINDING"
        by (metis WF_BINDING_predicate WF_RELATION_WF_ALPHA_PREDICATE assm(1))

      moreover with assm have b1wf:"?b1 \<in> WF_BINDING"
        apply(auto simp add:WF_BINDING_def COMPOSABLE_def HOMOGENEOUS_def)
        apply(simp add:dash_def)
      done 

      moreover have "?b1 \<cong> ?b2 on in a"
        by (simp add:beta_equiv_def)

      moreover then have "br = (?b \<oplus> ?b1 on in a) \<oplus> ?b2 on out (\<alpha> r)"
        by (smt beta_equiv_comm beta_equiv_override override_on_idem)

      moreover from assm have "\<forall>x\<in>in a \<union> undash ` out a. ?b1 x = ?b1 (dash x)"
        by (auto simp add:COMPOSABLE_def HOMOGENEOUS_def)

      ultimately show "\<exists>b1 b2 b.
              br = (b \<oplus> b1 on in a) \<oplus> b2 on out (\<alpha> r) \<and>
              b1 \<in> WF_BINDING \<and>
              (\<forall>x\<in>in a \<union> undash ` out a. b1 x = b1 (dash x)) \<and>
              b2 \<in> \<beta> r \<and> b \<in> WF_BINDING \<and> (\<forall>x\<in>in (\<alpha> r). b1 (dash x) = b2 x)"
        using assms 
        apply(rule_tac x="?b1" in exI)
        apply(rule_tac x="?b2" in exI)
        apply(rule_tac x="?b" in exI)
        apply(force)
      done
    qed
  qed

  ultimately show ?thesis
    by (metis pairI)
qed

lemma SemiR_dist_OrP:
      "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; r \<in> WF_RELATION
       ; COMPOSABLE (\<alpha> p) (\<alpha> r); COMPOSABLE (\<alpha> q) (\<alpha> r) \<rbrakk> \<Longrightarrow>
       (p \<or>p q) ; r = (p ; r) \<or>p (q ; r)"
apply(subgoal_tac "(p \<or>p q) \<in> WF_RELATION")
apply(subgoal_tac "COMPOSABLE (\<alpha> (p \<or>p q)) (\<alpha> r)")
apply(simp add:SemiR_def)
apply(simp add:WF_RELATION_def)
apply(utp_pred_eq_tac)
apply(rule conjI)
apply(clarify)
apply(simp add:COMPOSABLE_def WF_ALPHA_PREDICATE_def)
apply(blast)
apply(rule ballI)
apply(simp add:COMPOSABLE_def WF_ALPHA_PREDICATE_def)
apply(force)
apply(simp add:COMPOSABLE_def WF_RELATION_def)
apply(simp add:WF_RELATION_def)
done

lemma ConvR_invol:
  "\<lbrakk> r \<in> WF_RELATION \<rbrakk> \<Longrightarrow> r\<^sup>\<smile>\<^sup>\<smile> = r" 
apply (subgoal_tac "r\<^sup>\<smile> \<in> WF_RELATION")
apply (simp add:ConvR_def SS_conv_VAR_RENAME)
apply (metis SS_conv_VAR_RENAME SS_conv_invol RenameP_invol WF_RELATION_WF_ALPHA_PREDICATE)
apply (metis ConvR_closure)
done

lemma 
assumes "[(x,e)] \<in> WF_ASSIGNMENT a" "[(x,f)] \<in> WF_ASSIGNMENT a"
        "a \<in> WF_ALPHABET" "a \<subseteq> UNDASHED \<union> DASHED" "HOMOGENEOUS a"
shows "x :=\<^bsub>a\<^esub> e ; x :=\<^bsub>a\<^esub> f = x :=\<^bsub>a\<^esub> f"
proof -
  note assms

  moreover from assms have "x :=\<^bsub>a\<^esub> e \<in> WF_RELATION"
    by simp

  moreover from assms have "x :=\<^bsub>a\<^esub> f \<in> WF_RELATION"
    by simp

  moreover from assms have "COMPOSABLE (\<alpha> (x :=\<^bsub>a\<^esub> e)) (\<alpha> (x :=\<^bsub>a\<^esub> f))"
    by (simp add:COMPOSABLE_def utp_alphabet_simps)

  ultimately show ?thesis
    sorry

(*
  apply(simp add:SemiR_SemiB SemiB_def)
  apply(simp add:AssignR_def)
  apply(auto)
*)
qed
*)

   
end
end
