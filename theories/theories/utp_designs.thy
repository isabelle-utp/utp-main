(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* UTP Designs *}

theory utp_designs
imports "../alpha/utp_alpha_pred" "../alpha/utp_alpha_rel" "../alpha/utp_alpha_expr"
begin

context ALPHA_PRED_BOOL
begin

subsection {* Constructs *}

definition okay :: "'TYPE VAR" where
"okay \<equiv> (\<lparr>name_str = ''okay'',
         dashes = 0,
         subscript = NoSub\<rparr>, BoolType)"

definition okay' :: "'TYPE VAR" where
"okay' \<equiv> (\<lparr>name_str = ''okay'',
          dashes = 1,
          subscript = NoSub\<rparr>, BoolType)"

abbreviation OK where "OK \<equiv> {okay,okay'}"

abbreviation ok_true :: 
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_\<^sup>t" [150]) where
"p\<^sup>t \<equiv> p[true|okay]\<alpha>"

abbreviation ok_false :: 
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_\<^sup>f" [150]) where
"p\<^sup>f \<equiv> p[false|okay]\<alpha>"

abbreviation "ok  a \<equiv> &okay \<oplus>\<alpha> a"
abbreviation "ok' a \<equiv> &okay' \<oplus>\<alpha> a"


definition DesignD :: 
"('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE" (infixr "\<turnstile>" 60) where
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE; \<alpha> p = \<alpha> q \<rbrakk> \<Longrightarrow> 
   p \<turnstile> q \<equiv> (ok (\<alpha> p) \<and>\<alpha> p) \<Rightarrow>\<alpha> (ok' (\<alpha> q) \<and>\<alpha> q)"

definition SkipD ::
"'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("IID") where
"IID a = (true a \<turnstile> II\<alpha> a)"

definition "H1 \<equiv> \<lambda> x. ok (\<alpha> x) \<Rightarrow>\<alpha> x"

definition J :: "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"J a \<equiv> (ok a \<Rightarrow>\<alpha> ok' a) \<and>\<alpha> (II\<alpha> a)"

definition H2 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H2 \<equiv> \<lambda> p. (p ;\<alpha> J (\<alpha> p))"

definition H2' :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H2' \<equiv> \<lambda> p. [p\<^sup>t \<Rightarrow>\<alpha> (p\<^sup>f)]\<alpha>"

definition H3 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H3 \<equiv> \<lambda> p. p ;\<alpha> IID (\<alpha> p)"

definition H4 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H4 \<equiv> \<lambda> p. p ;\<alpha> true (\<alpha> p) \<Rightarrow>\<alpha> true (\<alpha> p)"

definition DESIGN_ALPHABET :: "'TYPE ALPHABET set"
where "DESIGN_ALPHABET = REL_ALPHABET \<inter> {a. OK \<subseteq> a}"

(*
{a. a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<union> DASHED \<and> OK \<subseteq> a}"
*)

(*
definition DESIGNS :: "('VALUE, 'TYPE) UTP_THEORY" where
"DESIGNS = \<lparr> utp_alphabets = WF_DESIGN_ALPHABET
           , healthconds = {H1, H2, H3, H4} \<rparr>"

definition WF_DESIGN where "WF_DESIGN = TheoryPreds DESIGNS"
*)

subsection {* Basic Laws *}

theorem WF_DESIGN_ALPHABET [closure]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> a \<in> REL_ALPHABET"
  by (simp add:DESIGN_ALPHABET_def)

theorem WF_DESIGN_UNDASHED_DASHED [closure]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> a \<subseteq> UNDASHED \<union> DASHED"
  by (simp add:DESIGN_ALPHABET_def REL_ALPHABET_def)

theorem okay_DESIGN_ALPHABET [elim]: 
"\<lbrakk> a \<in> DESIGN_ALPHABET; okay \<in> a \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:DESIGN_ALPHABET_def)

theorem okay'_DESIGN_ALPHABET [elim]: 
"\<lbrakk> a \<in> DESIGN_ALPHABET; okay' \<in> a \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:DESIGN_ALPHABET_def)

theorem UNDASHED_okay [simp]: "okay \<in> UNDASHED" 
  by (simp add:okay_def UNDASHED_def)

theorem DASHED_okay' [simp]: "okay' \<in> DASHED" 
  by (simp add:okay'_def DASHED_def)

subsection {* Basic Alphabet Laws *}

theorem ok_alphabet [alphabet]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> \<alpha> (ok a) = a"
  by (auto simp add:alphabet closure)

theorem ok'_alphabet [alphabet]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> \<alpha> (ok' a) = a"
  by (auto simp add:alphabet closure)

theorem DesignD_alphabet [alphabet]: 
"\<lbrakk>r1 \<in> WF_ALPHA_PREDICATE;
  r2 \<in> WF_ALPHA_PREDICATE;
  \<alpha> r1 = \<alpha> r2\<rbrakk> \<Longrightarrow>
  \<alpha> (r1 \<turnstile> r2) = \<alpha> r1 \<union> \<alpha> r2 \<union> OK"
  apply (simp add:DesignD_def)
  apply (simp add:alphabet closure)
  apply (force)
done

theorem SkipD_alphabet [alphabet]: "a \<in> REL_ALPHABET \<Longrightarrow> \<alpha> (IID a) = a \<union> OK"
  by (simp add: SkipD_def alphabet closure)

subsection {* Basic Closure Laws *}

lemma ok_pred [closure]: 
"\<lbrakk> a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<union> DASHED \<rbrakk> \<Longrightarrow> ok a \<in> WF_RELATION"
  by (force intro:WF_RELATION_intro simp add:closure alphabet)

lemma ok'_pred [closure]: 
"a \<in> WF_ALPHABET \<Longrightarrow> ok' a \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure)

lemma DesignD_rel_closure [closure]: 
"\<lbrakk> r1 \<in> WF_RELATION; r2 \<in> WF_RELATION; \<alpha> r1 = \<alpha> r2 \<rbrakk> \<Longrightarrow>
r1 \<turnstile> r2 \<in> WF_RELATION"
  apply (auto intro:closure simp add:DesignD_def WF_RELATION_def)
  apply (simp add:REL_ALPHABET_def)
  apply (simp add:alphabet closure)
done

lemma SkipD_closure [closure]: "a \<in> REL_ALPHABET \<Longrightarrow> IID a \<in> WF_RELATION"
  by (simp add:SkipD_def closure alphabet)

lemma J_closure [closure]: "a \<in> DESIGN_ALPHABET \<Longrightarrow> J a \<in> WF_RELATION"
  by (rule WF_RELATION_intro, simp_all add:closure alphabet J_def)

subsection {* Laws from the notes *}

theorem DesignD_extreme_point_true:
  assumes "a \<in> DESIGN_ALPHABET"
  shows "false a \<turnstile> false a = false a \<turnstile> true a"
  apply (insert assms)
  apply (simp add:DesignD_def closure alphabet)
  apply (utp_alpha_tac, utp_pred_auto_tac)
done

theorem DesignD_extreme_point_nok:
  assumes "a \<in> DESIGN_ALPHABET"
  shows "true a \<turnstile> false a = \<not>\<alpha> ok a"
proof -
  from assms have "true a \<turnstile> false a = (ok a \<and>\<alpha> true a \<Rightarrow>\<alpha> ok' a \<and>\<alpha> false a)"
    by (simp add:DesignD_def closure alphabet)

  also from assms have "... = ok a \<Rightarrow>\<alpha> ok' a \<and>\<alpha> false a"
    by (utp_alpha_tac, utp_pred_auto_tac)
  
  also from assms have "... = ok a \<Rightarrow>\<alpha> false a"
    by (utp_alpha_tac, utp_pred_auto_tac)

  ultimately show ?thesis using assms
    apply (utp_alpha_tac, utp_pred_auto_tac)
  done
qed

theorem DesignD_export_precondition:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "\<alpha> p = \<alpha> q"
  shows "p \<turnstile> q = p \<turnstile> p \<and>\<alpha> q"
proof -
  from assms have "p \<turnstile> q = ok (\<alpha> p) \<and>\<alpha> p \<Rightarrow>\<alpha> ok' (\<alpha> q) \<and>\<alpha> q"
    by (simp add:DesignD_def closure alphabet)

  also from assms have "... = ok (\<alpha> p) \<and>\<alpha> p \<Rightarrow>\<alpha> ok' (\<alpha> q) \<and>\<alpha> p \<and>\<alpha> q"
    by (utp_alpha_tac, utp_pred_auto_tac)

  ultimately show ?thesis using assms
    by (simp add:DesignD_def closure alphabet)
qed

theorem DesignD_refinement:
  assumes "p1 \<in> WF_RELATION" "p2 \<in> WF_RELATION" 
          "q1 \<in> WF_RELATION" "q2 \<in> WF_RELATION"
          "\<alpha> p1 = \<alpha> q1" "\<alpha> q1 = \<alpha> p2" "\<alpha> p2 = \<alpha> q2" 
  shows   "(p1 \<turnstile> q1) \<sqsubseteq>\<alpha> (p2 \<turnstile> q2) = [p1 \<Rightarrow>\<alpha> p2]\<alpha> \<and>\<alpha> [p1 \<and>\<alpha> q2 \<Rightarrow>\<alpha> q1]\<alpha>"
proof -
  from assms have "(p1 \<turnstile> q1) \<sqsubseteq>\<alpha> (p2 \<turnstile> q2) = [(p2 \<turnstile> q2) \<Rightarrow>\<alpha> (p1 \<turnstile> q1)]\<alpha>"
    by (simp add:RefA_lemma closure alphabet)

  also from assms 
  have "... = [(ok (\<alpha> p2) \<and>\<alpha> p2 \<Rightarrow>\<alpha> ok' (\<alpha> q2) \<and>\<alpha> q2) \<Rightarrow>\<alpha> (ok (\<alpha> p1) \<and>\<alpha> p1 \<Rightarrow>\<alpha> ok' (\<alpha> q1) \<and>\<alpha> q1)]\<alpha>"
    by (simp add:DesignD_def closure alphabet)
  
  also from assms
  have "... = [(p2 \<Rightarrow>\<alpha> ok' (\<alpha> q2) \<and>\<alpha> q2) \<Rightarrow>\<alpha> (p1 \<Rightarrow>\<alpha> ok' (\<alpha> q1) \<and>\<alpha> q1)]\<alpha>"
    apply (utp_alpha_tac)
    apply (utp_pred_auto_tac)
    (* Need more lemmas to get further ... *)
    oops

subsection {* Healthiness Laws properties *}

lemma H1_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H1 (H1 p) = H1 p"
  apply (simp add:H1_def WF_RELATION_def)
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
done

lemma J_split: 
  assumes "p \<in> WF_RELATION" 
  shows "p ;\<alpha> J (\<alpha> p) = p\<^sup>f \<or>\<alpha> (p\<^sup>t \<or>\<alpha> ok' (\<alpha> p))"
proof -
  from assms have "p ;\<alpha> J (\<alpha> p) = p ;\<alpha> (ok (\<alpha> p) \<Rightarrow>\<alpha> ok' (\<alpha> p)) \<and>\<alpha> II\<alpha> (\<alpha> p)"
    by (simp add: J_def)

  also from assms have "... = p ;\<alpha> (ok (\<alpha> p) \<Rightarrow>\<alpha> ok (\<alpha> p) \<and>\<alpha> ok' (\<alpha> p)) \<and>\<alpha> II\<alpha> (\<alpha> p)"
    oops

lemma H2_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H2 (H2 p) = H2 p"
  apply (simp add:H2_def)
  oops

lemma H3_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H3 (H3 p) = H3 p"
  apply (simp add:H3_def)
  oops

lemma H4_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H4 (H4 p) = H4 p"
  oops
  
subsection {* Design Closure Laws *}

(*
lemma DESIGNS_WF: "DESIGNS \<in> WF_UTP_THEORY"
proof (simp add:DESIGNS_def WF_UTP_THEORY_def, rule conjI)
  show wf_alpha:"WF_DESIGN_ALPHABET \<subseteq> WF_ALPHABET"
    by (force simp add:WF_DESIGN_ALPHABET_def)

  moreover from wf_alpha have "H1 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H1_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done

  moreover from wf_alpha have "H2 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H2_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done

  moreover from wf_alpha have "H3 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H3_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done

  moreover from wf_alpha have "H4 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H4_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done


  ultimately show "{H1, H2, H3, H4} \<in> WF_HEALTH_CONDS WF_DESIGN_ALPHABET"
    by (simp add:WF_HEALTH_CONDS_def)
qed
*)

lemma H1_closure[closure]: 
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> H1 p \<in> WF_ALPHA_PREDICATE"
  by (simp add:H1_def closure)


lemma H2_closure[closure]: 
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> H2 p \<in> WF_ALPHA_PREDICATE"
  oops

subsection {* Alphabet theorems *}

subsection {* Design properties *}
 

lemma H1_design: 
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow>
 (p \<turnstile> q) = H1 (p \<turnstile> q)"
  apply(simp add:DesignD_def H1_def)
  oops

end
end
