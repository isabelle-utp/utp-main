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

definition ok :: "'TYPE VAR" where
"ok \<equiv> (\<lparr>name_str = ''ok'',
        dashes = 0,
        subscript = NoSub\<rparr>, BoolType)"

definition ok' :: "'TYPE VAR" where
"ok' \<equiv> (\<lparr>name_str = ''ok'',
        dashes = 1,
        subscript = NoSub\<rparr>, BoolType)"

definition DesignD :: 
"('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ \<turnstile> _") where
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow> 
   p \<turnstile> q \<equiv> (&ok \<and>p p \<Rightarrow>p &ok' \<and>p q)"

definition H1 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H1 \<equiv> \<lambda> p. (&ok \<Rightarrow>p p)"

lemma H1_idempotent: "p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> (H1 \<circ> H1) p = H1 p"
apply(rule eval_intro)
apply(simp add:closure alpha_closure H1_def VarE_type ok_def)
apply(simp add:closure alpha_closure H1_def VarE_type ok_def)
apply(simp add:alphabet closure alpha_closure H1_def VarE_type ok_def)
apply(simp add:H1_def eval closure alpha_closure VarE_type ok_def) 
done

definition H2 :: "('VALUE, 'TYPE) ALPHA_FUNCTION" where
"H2 \<equiv> \<lambda> p. [p[true|ok'] \<Rightarrow>p p[false|ok']]"



end
end
