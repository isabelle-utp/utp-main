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

term "lvar_lift x \<times>\<^sub>L lvar_lift x"

term "lvar_lift snd\<^sub>L"

term "(lvar_lift snd\<^sub>L \<times>\<^sub>L lvar_lift snd\<^sub>L)"

term "P \<restriction>\<^sub>p (lvar_lift snd\<^sub>L \<times>\<^sub>L lvar_lift snd\<^sub>L)"

abbreviation lvlift :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>l") where "\<lceil>P\<rceil>\<^sub>l \<equiv> P \<oplus>\<^sub>p (lvar_lift snd\<^sub>L \<times>\<^sub>L lvar_lift snd\<^sub>L)"
abbreviation lvdrop :: "_ \<Rightarrow> _" ("\<lfloor>_\<rfloor>\<^sub>l") where "\<lfloor>P\<rfloor>\<^sub>l \<equiv> P \<restriction>\<^sub>p (lvar_lift snd\<^sub>L \<times>\<^sub>L lvar_lift snd\<^sub>L)"

text {* Lens representing local variables *}

definition "lvar = VAR lvar\<^sub>u"

text {* Lens representing global variables *}

definition "gvar = VAR more"

declare lvar_def [upred_defs]

lemma uvar_lvar [simp]: "uvar lvar"
  by (simp add: lvar_def, unfold_locales, simp_all)

lemma vwb_lens_uvar_lift [simp]: "vwb_lens X \<Longrightarrow> vwb_lens (lvar_lift X)"
  by (unfold_locales, simp_all add: lvar_lift_def)

lemma uvar_gvar [simp]: "uvar gvar"
  by (simp add: gvar_def, unfold_locales, simp_all)

lemma lvar_indep_gvar [simp]: "lvar \<bowtie> gvar" "gvar \<bowtie> lvar"
  by (auto intro:lens_indepI simp add: lvar_def gvar_def)

definition var_scope :: 
  "(('a \<Longrightarrow> ('a \<times> '\<L>, '\<alpha>) lvar_scheme) \<Rightarrow> (('a \<times> '\<L>, '\<alpha>) lvar_scheme) hrelation) \<Rightarrow>
   (('\<L>, '\<alpha>) lvar_scheme) hrelation" where
"var_scope P = (\<^bold>+(lvar_lift snd\<^sub>L) ;; P (fst\<^sub>L ;\<^sub>L lvar) ;; \<^bold>-(lvar_lift snd\<^sub>L))"

syntax
  "_var_scope" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("var _ \<bullet> _" [0,10] 10)
  "_var_scope_ty" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ : _ \<bullet> _" [0,0,10] 10)

translations
  "var x \<bullet> P" == "CONST var_scope (\<lambda> x. P)"
  "var x : 'a \<bullet> P" => "CONST var_scope (\<lambda> x :: ('a \<Longrightarrow> _). P)"

lemma lvar_assign_null:
  "(var x \<bullet> x := v) = II"
  apply (simp add: var_scope_def lvar_lift_def upred_defs urel_defs relcomp_unfold lens_comp_def fst_lens_def snd_lens_def)
  apply (transfer, simp add: relcomp_unfold, rule ext, simp add:prod.case_eq_if)
  apply (metis (no_types, lifting) fst_conv lvar.equality lvar.ext_inject lvar.select_convs(1) lvar.update_convs(1) sndI)
done

lemma "\<lbrakk> $lvar \<sharp> Q; $lvar\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> (var x \<bullet> P x ;; Q) = ((var x \<bullet> P x) ;; \<lfloor>Q\<rfloor>\<^sub>l)"
  apply (simp add: var_scope_def lvar_lift_def upred_defs urel_defs relcomp_unfold lens_comp_def fst_lens_def snd_lens_def prod_lens_def prod.case_eq_if)
  apply (transfer, simp add: relcomp_unfold prod.case_eq_if lens_create_def comp_def, rule ext)
  apply (safe)
  apply (simp)
  oops

end