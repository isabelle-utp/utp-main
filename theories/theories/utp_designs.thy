(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* UTP Designs *}

theory utp_designs
imports
  "../alpha/utp_alpha_rel"
(* "../alpha/utp_alpha_expr" *)
begin

subsection {* Auxiliary Variables *}

definition ok :: "('TYPE :: BOOL_TYPE) VAR" where
"ok = (\<lparr>name_str = ''ok'', dashes = 0, subscript = NoSub\<rparr>, BoolType)"

definition ok' :: "('TYPE :: BOOL_TYPE) VAR" where
"ok' \<equiv> (\<lparr>name_str = ''ok'', dashes = 1, subscript = NoSub\<rparr>, BoolType)"

definition DESIGN_VAR :: "('TYPE :: BOOL_TYPE) VAR set" where
"DESIGN_VAR = {ok, ok'}"

context ALPHA_PRED_BOOL
begin

subsection {* Substitutions *}

abbreviation ok_true ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_\<^sup>t" [150]) where
"p\<^sup>t \<equiv> p[true|ok]\<alpha>"

abbreviation ok_false ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_\<^sup>f" [150]) where
"p\<^sup>f \<equiv> p[false|ok]\<alpha>"

subsection {* Operators *}

subsubsection {* Design Construct *}

definition DesignD ::
"('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ \<turnstile> _") where
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
   p \<turnstile> q \<equiv> (&ok \<and>\<alpha> p \<Rightarrow>\<alpha> &ok' \<and>\<alpha> q)"

subsubsection {* Design Skip *}

definition SkipD ::
"'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("IID") where
"IID a = (true a \<turnstile> II\<alpha> a)"

definition H1 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H1 \<equiv> (\<lambda> p. (&ok \<Rightarrow>\<alpha> p))"

abbreviation J ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"J a \<equiv> (&ok \<Rightarrow>\<alpha> &ok') \<and>\<alpha> (IID a)"

definition H2 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H2 \<equiv> \<lambda> p. (p ;\<alpha> J (\<alpha> p))"

definition H2' :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H2' \<equiv> \<lambda> p. [p\<^sup>t \<Rightarrow>\<alpha> (p\<^sup>f)]\<alpha>"

definition H3 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H3 \<equiv> \<lambda> p. p ;\<alpha> IID (\<alpha> p)"

definition H4 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H4 \<equiv> \<lambda> p. (p ;\<alpha> true (\<alpha> p)) \<Rightarrow>\<alpha> true (\<alpha> p)"

definition WF_DESIGN_ALPHABET :: "'TYPE ALPHABET set" where
"WF_DESIGN_ALPHABET =
 {a. a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<union> DASHED \<and> DESIGN_VAR \<subseteq> a}"

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

(*
definition DESIGNS :: "('VALUE, 'TYPE) UTP_THEORY" where
"DESIGNS = \<lparr> utp_alphabets = WF_DESIGN_ALPHABET
           , healthconds = {H1, H2, H3, H4} \<rparr>"

definition WF_DESIGN where "WF_DESIGN = TheoryPreds DESIGNS"
*)

subsection {* Basic Laws *}

theorem UNDASHED_ok [simp]: "ok \<in> UNDASHED"
  by (simp add:ok_def UNDASHED_def)

theorem DASHED_ok' [simp]: "ok' \<in> DASHED"
  by (simp add:ok'_def DASHED_def)

subsection {* Basic Closure Laws *}

lemma ok_pred [closure]: "&ok \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure)

lemma ok'_pred [closure]: "&ok' \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure)

lemma DesignD_rel_closure [closure]:
"\<lbrakk> r1 \<in> WF_RELATION; r2 \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
r1 \<turnstile> r2 \<in> WF_RELATION"
  apply (auto intro:closure simp add:DesignD_def WF_RELATION_def)
  apply (simp add:REL_ALPHABET_def)
  apply (simp add:alphabet closure)
done

lemma SkipD_closure [closure]: "a \<in> REL_ALPHABET \<Longrightarrow> IID a \<in> WF_RELATION"
  apply (simp add:SkipD_def)
  apply (auto intro: closure)
done

lemma J_closure [closure]: "a \<in> REL_ALPHABET \<Longrightarrow> J a \<in> WF_RELATION"
  by (simp add: closure)

subsection {* Basic Alphabet Laws *}

theorem DesignD_alphabet [alphabet]:
"\<lbrakk>r1 \<in> WF_ALPHA_PREDICATE;
  r2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
  \<alpha> (r1 \<turnstile> r2) = \<alpha> r1 \<union> \<alpha> r2 \<union> OK"
  apply (simp add:DesignD_def)
  apply (simp add:alphabet closure)
  apply (force)
done

theorem SkipD_alphabet [alphabet]: "a \<in> REL_ALPHABET \<Longrightarrow> \<alpha> (IID a) = a \<union> OK"
  by (simp add: SkipD_def alphabet closure)

subsection {* Healthiness Laws properties *}

lemma H1_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H1 (H1 p) = H1 p"
  apply (simp add:H1_def WF_RELATION_def)
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
done

lemma J_split: "p \<in> WF_RELATION \<Longrightarrow> p ;\<alpha> J (\<alpha> p) = p\<^sup>f \<or>\<alpha> (p\<^sup>t \<or>\<alpha> &ok')"
  sorry

lemma H2_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H2 (H2 p) = H2 p"
  apply (simp add:H2_def)
  oops

lemma H3_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H3 (H3 p) = H3 p"
  oops

lemma H4_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H4 (H4 p) = H4 p"
  oops

subsection {* Closure Laws *}

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
  apply(utp_alpha_tac, utp_pred_tac)
  apply(auto)
done

end
end
