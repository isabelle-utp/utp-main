section {* Relational alphabet extension and local variables *}

theory utp_lvar
imports utp_rel
begin

subsection {* Relational alphabet extension and restriction *}

lift_definition rel_aext :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha>, '\<beta>) relation" ("\<^bold>+'(_')")
is "\<lambda> x (s, s'). s' = put\<^bsub>x\<^esub> s' s" .

lift_definition rel_ares :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<beta>, '\<alpha>) relation" ("\<^bold>-'(_')")
is "\<lambda> x (s, s'). s = put\<^bsub>x\<^esub> s s'" .

lemma rel_aext_ares:
  "mwb_lens x \<Longrightarrow> (\<^bold>+(x) ;; \<^bold>-(x)) = II"
  apply (simp add: urel_defs)
  apply (transfer)
  apply (rule ext)
  apply (simp add: relcomp_unfold prod.case_eq_if)
  apply (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)
done

subsection {* Local variables *}

record '\<L> lvar =
  lvar\<^sub>u :: "'\<L>"

definition lvar_lift :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('a, '\<alpha>) lvar_scheme \<Longrightarrow> ('b, '\<alpha>) lvar_scheme" where
"lvar_lift X = \<lparr> lens_get = \<lambda> s. \<lparr> lvar\<^sub>u = get\<^bsub>X\<^esub> (lvar\<^sub>u s), \<dots> = more s \<rparr>
               , lens_put = \<lambda> s v. \<lparr> lvar\<^sub>u = put\<^bsub>X\<^esub> (lvar\<^sub>u s) (lvar\<^sub>u v), \<dots> = more v \<rparr> \<rparr>"

definition "lvar = VAR lvar\<^sub>u"

declare lvar_def [upred_defs]

lemma uvar_lvar [simp]: "uvar lvar"
  by (simp add: lvar_def, unfold_locales, simp_all)

lemma vwb_lens_uvar_lift [simp]: "vwb_lens X \<Longrightarrow> vwb_lens (lvar_lift X)"
  by (unfold_locales, simp_all add: lvar_lift_def)

definition var_scope :: 
  "(('a \<Longrightarrow> ('a \<times> '\<L>, '\<alpha>) lvar_scheme) \<Rightarrow> (('a \<times> '\<L>, '\<alpha>) lvar_scheme) hrelation) \<Rightarrow>
   (('\<L>, '\<alpha>) lvar_scheme) hrelation" where
"var_scope P = (\<^bold>+(lvar_lift snd\<^sub>L) ;; P (fst\<^sub>L ;\<^sub>L lvar) ;; \<^bold>-(lvar_lift snd\<^sub>L))"

syntax
  "_var_scope" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ : _ \<bullet> _" [0,0,100] 100)

translations
  "var x : 'a \<bullet> P" == "CONST var_scope (\<lambda> x :: ('a \<Longrightarrow> _). P)"

end