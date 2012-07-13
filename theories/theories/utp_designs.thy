(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/theories/utp_designs.thy                                         *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* UTP Designs *}

theory utp_designs
imports "../theories/utp_theory" utp_rel
begin

context GEN_EXPR
begin

subsection {* Constructs *}

definition ok :: "'TYPE VAR" where
"ok \<equiv> (\<lparr>name_str = ''ok'',
        dashes = 0,
        subscript = NoSub\<rparr>, BoolType)"

definition ok' :: "'TYPE VAR" where
"ok' \<equiv> (\<lparr>name_str = ''ok'',
        dashes = 1,
        subscript = NoSub\<rparr>, BoolType)"

abbreviation OK where "OK \<equiv> {ok,ok'}"

abbreviation ok_true :: 
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_\<^sup>t" [150]) where
"p\<^sup>t \<equiv> p[true|ok]"

abbreviation ok_false :: 
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_\<^sup>f" [150]) where
"p\<^sup>f \<equiv> p[false|ok]"

definition DesignD :: 
"('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ \<turnstile> _") where
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow> 
   p \<turnstile> q \<equiv> (&ok \<and>p p \<Rightarrow>p &ok' \<and>p q)"

definition SkipD ::
"'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<Pi>D") where
"\<Pi>D a = (true a \<turnstile> \<Pi> a)"

definition H1 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H1 \<equiv> \<lambda> p. (&ok \<Rightarrow>p p)"

abbreviation J :: "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"J a \<equiv> (&ok \<Rightarrow>p &ok') \<and>p (\<Pi>D a)"

definition H2 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H2 \<equiv> \<lambda> p. (p ; J (\<alpha> p))"

definition H2' :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H2' \<equiv> \<lambda> p. [p\<^sup>t \<Rightarrow>p (p\<^sup>f)]"

definition H3 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H3 \<equiv> \<lambda> p. p ; \<Pi>D (\<alpha> p)"

definition H4 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H4 \<equiv> \<lambda> p. (p ; true (\<alpha> p)) \<Rightarrow>p true (\<alpha> p)"

definition WF_DESIGN_ALPHABET :: "'TYPE ALPHABET set"
where "WF_DESIGN_ALPHABET = {a. a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<union> DASHED \<and> OK \<subseteq> a}"

definition DESIGNS :: "('VALUE, 'TYPE) UTP_THEORY" where
"DESIGNS = \<lparr> utp_alphabets = WF_DESIGN_ALPHABET
           , healthconds = {H1, H2, H3, H4} \<rparr>"

definition WF_DESIGN where "WF_DESIGN = TheoryPreds DESIGNS"

subsection {* Basic Closure Laws *}

lemma ok_pred[closure]: "&ok \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure alpha_closure VarE_type ok_def)

lemma ok'_pred[closure]: "&ok' \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure alpha_closure VarE_type ok'_def)

subsection {* Healthiness Laws properties *}

lemma H1_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H1 (H1 p) = H1 p"
  by (simp add:H1_def WF_RELATION_def, utp_pred_eq_tac)

lemma H2_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H2 (H2 p) = H2 p"
  sorry

lemma H3_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H3 (H3 p) = H3 p"
  sorry

lemma H4_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H4 (H4 p) = H4 p"
  sorry
  
subsection {* Closure Laws *}

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

lemma H1_closure[closure]: 
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> H1 p \<in> WF_ALPHA_PREDICATE"
  by (simp add:H1_def closure)

lemma J_closure[closure]:
"a \<in> WF_ALPHABET \<Longrightarrow> J a \<in> WF_ALPHA_PREDICATE"
  sorry

lemma H2_closure[closure]: 
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> H2 p \<in> WF_ALPHA_PREDICATE"
  sorry

subsection {* Alphabet theorems *}

subsection {* Design properties *}
 

lemma H1_design: 
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow>
 (p \<turnstile> q) = H1 (p \<turnstile> q)"
  apply(simp add:DesignD_def H1_def)
  apply(utp_pred_taut_tac)
  apply(auto)
done

lemma H1_left_zero: 
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; p = H1 p \<rbrakk> \<Longrightarrow> true (\<alpha> p) ; p = true (\<alpha> p)"
  sorry


lemma H2_design: 
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow>
 (p \<turnstile> q) = H2 (p \<turnstile> q)"
  apply(simp add:DesignD_def H2_def)
  apply(rule eval_intro)
  apply(simp add:closure alpha_closure alphabet)
  apply(simp add:closure alpha_closure alphabet)
sorry

end
end
