section \<open> Circus Core Types \<close>

theory utp_circus_core
  imports "UTP-Reactive-Designs.utp_rea_designs"
begin

subsection \<open> Circus Alphabet \<close>

alphabet '\<phi> csp_vars = "'\<sigma> rsp_vars" +
  ref :: "'\<phi> set"

text \<open>
  The following two locale interpretations are a technicality to improve the
  behaviour of the automatic tactics. They enable (re)interpretation of state
  spaces in order to remove any occurrences of lens types, replacing them by
  tuple types after the tactics @{method pred_simp} and @{method rel_simp}
  are applied. Eventually, it would be desirable to automate preform these
  interpretations automatically as part of the @{command alphabet} command.
\<close>

interpretation alphabet_csp_prd:
  lens_interp "\<lambda>(ok, wait, tr, m). (ok, wait, tr, ref\<^sub>v m, more m)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_csp_rel:
  lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', m, m').
    (ok, ok', wait, wait', tr, tr', ref\<^sub>v m, ref\<^sub>v m', more m, more m')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

type_synonym ('\<sigma>,'\<phi>) st_csp = "('\<sigma>, '\<phi> list, ('\<phi>, unit) csp_vars_scheme) rsp"
type_synonym ('\<sigma>,'\<phi>) action  = "('\<sigma>,'\<phi>) st_csp hrel"
type_synonym '\<phi> csp = "(unit,'\<phi>) st_csp"
type_synonym '\<phi> rel_csp  = "'\<phi> csp hrel"
  
text \<open> There is some slight imprecision with the translations, in that we don't bother to check
  if the trace event type and refusal set event types are the same. Essentially this is because
  its very difficult to construct processes where this would be the case. However, it may
  be better to add a proper ML print translation in the future. \<close>
  
translations
  (type) "('\<sigma>,'\<phi>) st_csp" <= (type) "('\<sigma>, '\<phi> list, '\<phi>1 csp_vars) rsp"
  (type) "('\<sigma>,'\<phi>) action" <= (type) "('\<sigma>, '\<phi>) st_csp hrel"
  
notation csp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>c")
notation csp_vars_child_lens ("\<Sigma>\<^sub>C")

subsection \<open> Basic laws \<close>

lemma R2c_tr_ext: "R2c ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>)"
  by (rel_auto)

subsection \<open> Unrestriction laws \<close>

lemma pre_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
  by (simp add: pre\<^sub>R_def unrest)

lemma peri_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> peri\<^sub>R(P)"
  by (simp add: peri\<^sub>R_def unrest)

lemma post_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> post\<^sub>R(P)"
  by (simp add: post\<^sub>R_def unrest)

lemma cmt_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"
  by (simp add: cmt\<^sub>R_def unrest)

lemma st_lift_unrest_ref' [unrest]: "$ref\<acute> \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)

lemma RHS_design_ref_unrest [unrest]:
  "\<lbrakk>$ref \<sharp> P; $ref \<sharp> Q \<rbrakk> \<Longrightarrow> $ref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q))\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma R1_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R1_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R2s_notin_ref': "R2s(\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) = (\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (pred_auto)

end