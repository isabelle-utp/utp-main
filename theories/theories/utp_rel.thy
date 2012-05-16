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

definition SkipR :: 
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<Pi>_") where
"a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<longrightarrow> \<Pi> a = (a \<union> dash ` a , { b . (b \<in> WF_BINDING) \<and> (\<forall> x \<in> a . b x = b (dash x)) })"

text {* Configure theorems for the predicate proof tactic. *}

lemma EvalP_SemiR[eval]: "\<lbrakk> r1 \<in> WF_RELATION; r2 \<in> WF_RELATION; COMPOSABLE (\<alpha> r1) (\<alpha> r2) \<rbrakk> \<Longrightarrow>
                    EvalP (r1 ; r2) b = EvalP (\<exists>-p dash ` (out (\<alpha> r1)) . r1[SS1] \<and>p r2[SS2]) b"
  by (simp add:SemiR_def)

declare CondR_def [eval]
 declare SemiR_def [eval]
declare SkipR_def [eval]

subsection {* Theorems *}

subsubsection {* Restrictions *}

theorem WF_RELATION_WF_ALPHA_PREDICATE :
"p \<in> WF_RELATION \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_RELATION_def)
done

theorem WF_RELATION_WF_ALPHABET[intro] :
"p \<in> WF_RELATION \<Longrightarrow> \<alpha> p \<in> WF_ALPHABET"
apply (auto simp add: WF_RELATION_def)
done

declare WF_RELATION_WF_ALPHA_PREDICATE [eval]
declare WF_RELATION_WF_ALPHABET [eval]

subsubsection {* Substitutions *}

lemma SS1_range_total: "x \<in> range SS1"
  apply(case_tac x, case_tac a)
  apply(simp add:SS1_def image_def dash_def undash_def)
  apply(smt fst_conv NAME.simps(1-3) snd_conv)
done

theorem SS1_VAR_SUBST [simp,intro] : "SS1 \<in> VAR_SUBST"
  apply(auto simp add:VAR_SUBST_def SS1_def bij_def inj_on_def undash_def dash_def)
  apply(smt NAME.equality prod_eq_iff unit.exhaust)+
  apply(rule SS1_range_total)
done

lemma SS1_dashes[simp,intro,eval]: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> SS1 ` a = in a \<union> dash ` (out a)"
  by (force simp add: SS1_def DASHED_def UNDASHED_def Un_def in_alphabet_def out_alphabet_def image_def SS1_def)

lemma SS2_range_total: "x \<in> range SS2"
  apply(case_tac x, case_tac a)
  apply(simp add:SS2_def image_def dash_def undash_def)
  apply(smt fst_conv NAME.simps(1-3) snd_conv)
done

theorem SS2_VAR_SUBST [simp,intro] :  "SS2 \<in> VAR_SUBST"
  apply(auto simp add:VAR_SUBST_def SS2_def bij_def inj_on_def undash_def dash_def)
  apply(smt NAME.equality prod_eq_iff unit.exhaust)+
  apply(rule SS2_range_total)
done

lemma SS2_dashes[simp,intro,eval]: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> SS2 ` a = (dash ` dash ` in a) \<union> (out a)"
  apply(auto simp add: SS2_def DASHED_def UNDASHED_def Un_def in_alphabet_def out_alphabet_def)
  apply(simp_all add:image_def SS2_def)
  apply(rule bexI, auto)+
done

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
assumes assm: "r1 \<in> WF_RELATION" "r2 \<in> WF_RELATION" "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
shows "\<alpha> (r1 ; r2) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
proof (insert assm, utp_pred_eq_tac)
  from assm have "\<alpha> r1 \<subseteq> UNDASHED \<union> DASHED" "\<alpha> r2 \<subseteq> UNDASHED \<union> DASHED"
                 "\<alpha> r1 \<in> WF_ALPHABET" "\<alpha> r2 \<in> WF_ALPHABET"
    by (auto simp add:WF_RELATION_def)
  with assm show "(SS1 ` \<alpha> r1 \<union> SS2 ` \<alpha> r2) - dash ` out (\<alpha> r1) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
    apply(auto simp add:COMPOSABLE_def)
    apply(simp add: dash_def in_alphabet_def UNDASHED_def)
    apply(simp add: dash_def out_alphabet_def DASHED_def)
  done
qed


theorem SkipR_alphabet [simp]:
"\<lbrakk> a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<rbrakk> \<Longrightarrow> \<alpha> (\<Pi> a) = a \<union> dash ` a"
 by (simp add: SkipR_def)


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

theorem SemiR_closure [simp, eval]:
  assumes assm: "r1 \<in> WF_RELATION" "r2 \<in> WF_RELATION" "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
  shows  "r1 ; r2 \<in> WF_RELATION"
proof -
  from assm have "r1 ; r2 \<in> WF_ALPHA_PREDICATE"
    by (utp_pred_eq_tac)

  with assm show ?thesis
    by (auto simp add: WF_RELATION_def in_alphabet_def out_alphabet_def)
qed

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

thm COMPOSABLE_def

theorem semi_assoc:
 assumes assm: "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION"
               "COMPOSABLE (\<alpha> p) (\<alpha> q)" "COMPOSABLE (\<alpha> q) (\<alpha> r)"
 shows "p ; (q ; r) = (p ; q) ; r"
proof -
  from assm have r1:"q ; r \<in> WF_RELATION" "p ; q \<in> WF_RELATION"
    by (auto)

  from assm have r2:"COMPOSABLE (\<alpha> p) (\<alpha> (q ; r))" "COMPOSABLE (\<alpha> (p ; q)) (\<alpha> r)"
    by(auto elim!:COMPOSABLE_elim)    

  from r1 r2 assm show ?thesis
    apply(utp_pred_eq_tac)
    apply(safe)
  sorry
qed

end
end
