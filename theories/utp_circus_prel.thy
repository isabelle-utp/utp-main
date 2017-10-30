(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus_prel.thy                                                  *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 18 Sep 2017 *)

section {* {\Circus} Preliminaries *}

theory utp_circus_prel
imports utp_theories_deep
begin

text {* Hide HOL's @{typ "'a rel"} type once again. *}

text {* TODO: The recall package ought to hide type syntax too! *}

hide_type (open) Relation.rel

type_synonym 'a hol_rel = "'a Relation.rel"

translations (type) "'a hol_rel" \<rightleftharpoons> (type)"'a Relation.rel"

subsection {* Syntax Adjustments *}

no_translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a()\<guillemotright> P"

subsection {* Channel Events *}

text {*
  The @{text "\<epsilon>(c)"} operator defined below yields the possible events for some
  channel @{text c}. It is useful to construct synchronisation sets of parallel
  compositions, for instance.
*}

definition events :: "('a, '\<epsilon>) chan \<Rightarrow> '\<epsilon> set" ("\<epsilon>'(_')") where
"events c = c ` UNIV"

subsection {* Proof Support *}

declare des_vars.extend_def [lens_defs]
declare des_vars.truncate_def [lens_defs]
declare rp_vars.extend_def [lens_defs]
declare rp_vars.truncate_def [lens_defs]
declare rsp_vars.extend_def [lens_defs]
declare rsp_vars.truncate_def [lens_defs]
declare csp_vars.extend_def [lens_defs]
declare csp_vars.truncate_def [lens_defs]

subsection {* State Hiding *}

text {* Note that the following lemma does not hold! *}

lemma hide_state_ex_cancel [simp]:
"abs_st (\<exists> {$st,$st\<acute>} \<bullet> P) = abs_st P"
apply (rel_auto)
oops

text \<open>Laws for the pre-, peri- and postcondition of @{const abs_st}\<close>

lemma pre\<^sub>R_abs_st [rdes]:
"pre\<^sub>R(abs_st P) = abs_st(pre\<^sub>R(P))"
apply (rel_auto)
done

lemma peri\<^sub>R_abs_st [rdes]:
"peri\<^sub>R(abs_st P) = abs_st(peri\<^sub>R(P))"
apply (rel_auto)
done

lemma post\<^sub>R_abs_st [rdes]:
"post\<^sub>R(abs_st P) = abs_st(post\<^sub>R(P))"
apply (rel_auto)
done

text \<open>Closure Laws\<close>

lemma abs_st_CSP_closure [closure]:
"P is CSP \<Longrightarrow> abs_st (\<exists> {$st, $st\<acute>} \<bullet> P) is CSP"
  by (metis SRD_state_srea state_srea_def)

subsection {* Instantiations *}

text {* Move this to the theory @{theory utp_dvar}. [TODO] *}

instantiation vstore :: vst
begin
definition vstore_lens_vstore :: "vstore \<Longrightarrow> vstore" where
"vstore_lens_vstore = 1\<^sub>L"
instance
apply (intro_classes)
apply (unfold vstore_lens_vstore_def)
apply (rule id_vwb_lens)
done
end
end