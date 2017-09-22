(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_hoare_ext.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)

section {* Hoare Logic Extensions *}

theory utp_hoare_ext
imports utp_hoare
begin

subsection {* Invariant Split Tactic *}

text {* This tactic is slightly more efficient than @{method hoare_split}. *}

named_theorems hoare_split_inv_laws "splitting laws for Hoare logic"

lemmas seq_hoare_inv = seq_hoare_invariant

lemma skip_hoare_aux:
"\<lbrace>p \<and> q\<rbrace>II\<lbrace>p\<rbrace>\<^sub>u" by (rel_simp)+

lemma cond_hoare_r':
"\<lbrakk>\<lbrace>p \<and> b\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u ; \<lbrace>p \<and> \<not>b\<rbrace>T\<lbrace>q\<rbrace>\<^sub>u\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>S \<triangleleft> b \<triangleright>\<^sub>r T\<lbrace>q\<rbrace>\<^sub>u"
  by (rel_auto)

declare hoare_r_conj [hoare_split_inv_laws]
declare skip_hoare_r [hoare_split_inv_laws]
declare skip_hoare_aux [hoare_split_inv_laws]
declare assigns_hoare_r [hoare_split_inv_laws]
declare seq_hoare_inv [hoare_split_inv_laws]
declare cond_hoare_r' [hoare_split_inv_laws]
declare while_hoare_r [hoare_split_inv_laws]
declare while_invr_hoare_r [hoare_split_inv_laws]

method hoare_split_inv uses add =
  (rule hoare_split_inv_laws add; (hoare_split_inv add: add))?
end