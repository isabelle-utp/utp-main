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

definition SkipR ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<Pi>_") where
"a \<in> WF_ALPHABET \<and>
 a \<subseteq> UNDASHED \<longrightarrow>
 \<Pi> a = LiftP (a \<union> dash ` a) (\<lambda> b . \<forall> x \<in> a . b x = b (dash x))"

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

declare SkipR_def [eval]
declare CondR_def [eval]
declare SemiR_def [eval]

subsection {* Theorems *}

subsubsection {* Restrictions *}

theorem WF_RELATION_WF_ALPHA_PREDICATE :
"p \<in> WF_RELATION \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_RELATION_def)
done

declare WF_RELATION_WF_ALPHA_PREDICATE [eval]

text {* Added by Simon. Do we really need this law? *}

theorem WF_RELATION_alphabet [intro] :
"p \<in> WF_RELATION \<Longrightarrow> \<alpha> p \<in> WF_ALPHABET"
apply (auto simp add: WF_RELATION_def)
done

declare WF_RELATION_alphabet [eval]

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

(* The following theorems do not seem to proof on my machine. Ask Simon. *)

(*
theorem SS1_range_total : "x \<in> range SS1"
apply (case_tac x, case_tac a)
apply (simp add : SS1_def image_def dash_def undash_def)
apply (smt fst_conv NAME.simps(1-3) snd_conv)
done

theorem SS1_VAR_SUBST [simp, intro] : "SS1 \<in> VAR_SUBST"
apply (auto simp
  add : VAR_SUBST_def SS1_def bij_def inj_on_def undash_def dash_def)
apply (smt NAME.equality prod_eq_iff unit.exhaust)+
apply (rule SS1_range_total)
done

theorem SS1_dashes[simp, intro, eval] :
"a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> SS1 ` a = in a \<union> dash ` (out a)"
apply (force simp add: SS1_def DASHED_def UNDASHED_def
  Un_def in_alphabet_def out_alphabet_def image_def SS1_def)
done

theorem SS2_range_total : "x \<in> range SS2"
apply (case_tac x, case_tac a)
apply (simp add:SS2_def image_def dash_def undash_def)
apply (smt fst_conv NAME.simps(1-3) snd_conv)
done

theorem SS2_VAR_SUBST [simp, intro] : "SS2 \<in> VAR_SUBST"
apply (auto simp add : VAR_SUBST_def SS2_def bij_def inj_on_def undash_def dash_def)
apply (smt NAME.equality prod_eq_iff unit.exhaust)+
apply (rule SS2_range_total)
done

theorem SS2_dashes[simp, intro, eval] :
"a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> SS2 ` a = (dash ` dash ` in a) \<union> (out a)"
apply (auto simp
  add: SS2_def DASHED_def UNDASHED_def Un_def in_alphabet_def out_alphabet_def)
apply (simp_all add:image_def SS2_def)
apply (rule bexI, auto)+
done
*)

subsubsection {* Alphabet Theorems *}

theorem WF_BINDING_FUN_SkipR [simp] :
"(\<lambda> b . \<forall> x \<in> a . f (b x) (b (dash x))) \<in> WF_BINDING_FUN (a \<union> dash ` a)"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: beta_equiv_def)
done

theorem SkipR_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 a \<subseteq> UNDASHED\<rbrakk> \<Longrightarrow>
 \<alpha> (\<Pi> a) = a \<union> dash ` a"
apply (simp add: SkipR_def)
done

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

(* The following theorem does not seem to proof on my machine. Ask Simon. *)

(*
theorem SemiR_alphabet [simp] :
assumes assm:
  "r1 \<in> WF_RELATION"
  "r2 \<in> WF_RELATION"
  "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
shows "\<alpha> (r1 ; r2) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
proof (insert assm, utp_pred_eq_tac)
  from assm have
    "\<alpha> r1 \<subseteq> UNDASHED \<union> DASHED"
    "\<alpha> r2 \<subseteq> UNDASHED \<union> DASHED"
    "\<alpha> r1 \<in> WF_ALPHABET"
    "\<alpha> r2 \<in> WF_ALPHABET"
      by (auto simp add: WF_RELATION_def)

  with assm show
    "(SS1 ` \<alpha> r1 \<union> SS2 ` \<alpha> r2) - dash ` out (\<alpha> r1) = in (\<alpha> r1) \<union> out (\<alpha> r2)"
      apply (auto simp add: COMPOSABLE_def)
      apply (simp add: dash_def in_alphabet_def UNDASHED_def)
      apply (simp add: dash_def out_alphabet_def DASHED_def)
  done
qed
*)

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

theorem SemiR_closure [simp]:
assumes assm:
  "r1 \<in> WF_RELATION"
  "r2 \<in> WF_RELATION"
  "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
shows "r1 ; r2 \<in> WF_RELATION"
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

theorem SemiR_assoc:
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 r3 \<in> WF_RELATION;
 COMPOSABLE (\<alpha> r1) (\<alpha> r2);
 COMPOSABLE (\<alpha> r2) (\<alpha> r3)\<rbrakk> \<Longrightarrow>
 r1 ; (r2 ; r3) = (r1 ; r2) ; r3"
apply (subgoal_tac "r2 ; r3 \<in> WF_RELATION");
apply (subgoal_tac "r1 ; r2 \<in> WF_RELATION");
apply (subgoal_tac "COMPOSABLE (\<alpha> r1) (\<alpha> (r2 ; r3))")
apply (subgoal_tac "COMPOSABLE (\<alpha> (r1 ; r2)) (\<alpha> r3)")
apply (simp add: SemiR_def)
apply (simp_all)
oops

(* The following theorem does not seem to proof on my machine. Ask Simon. *)

(*
theorem SemiR_assoc:
assumes assm:
  "r1 \<in> WF_RELATION"
  "r2 \<in> WF_RELATION"
  "r3 \<in> WF_RELATION"
  "COMPOSABLE (\<alpha> r1) (\<alpha> r2)"
  "COMPOSABLE (\<alpha> r2) (\<alpha> r3)"
shows "r1 ; (r2 ; r2) = (r1 ; r2) ; r3"
proof -
  from assm have r1 :
    "r1 ; r2 \<in> WF_RELATION"
    "r2 ; r3 \<in> WF_RELATION"
      by (simp_all)

  from assm have r2 :
    "COMPOSABLE (\<alpha> p) (\<alpha> (q ; r))"
    "COMPOSABLE (\<alpha> (p ; q)) (\<alpha> r)"
      by (auto elim! : COMPOSABLE_elim)

  from r1 r2 assm show ?thesis
    apply(utp_pred_eq_tac)
    apply(safe)
  sorry
qed
*)
end
end