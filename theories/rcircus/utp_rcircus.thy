section \<open> Experiment in creating Circus with a Refusal Testing Semantics \<close>

theory utp_rcircus
  imports Refusal_Tests "UTP-Reactive-Designs.utp_rea_designs"
begin

recall_syntax

subsection \<open> Refusal Syntax\<close>

syntax
  "_urmember"     :: "logic \<Rightarrow> logic \<Rightarrow> logic"  ("(_/ \<in>\<^sup>\<R> _)" [51, 51] 50)
  "_urnot_member" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  ("(_/ \<notin>\<^sup>\<R> _)" [51, 51] 50)
  "_urevevent"    :: "logic \<Rightarrow> logic" ("revent\<^sub>u'(_')")

term not_upred

translations 
  "(x \<in>\<^sup>\<R> A)" == "CONST bop (CONST rmember) x A"
  "(x \<notin>\<^sup>\<R> A)" == "CONST not_upred (x \<in>\<^sup>\<R> A)"
  "revent\<^sub>u(a)" == "CONST uop CONST revent a"

subsection \<open> Refusal Circus Alphabet \<close>

alphabet ('\<sigma>, '\<phi>) rcsp_vars = "('\<phi> list, '\<sigma>) rsp_vars" +
  rref :: "'\<phi> refusal"


type_synonym ('\<sigma>,'\<phi>) raction  = "('\<sigma>,'\<phi>) rcsp_vars hrel"
  
text \<open> There is some slight imprecision with the translations, in that we don't bother to check
  if the trace event type and refusal set event types are the same. Essentially this is because
  its very difficult to construct processes where this would be the case. However, it may
  be better to add a proper ML print translation in the future. \<close>
  
subsection \<open> Basic laws \<close>

lemma R2c_tr_ext: "R2c (U($tr\<acute> = $tr @ [\<lceil>a\<rceil>\<^sub>S\<^sub><])) = U($tr\<acute> = $tr @ [\<lceil>a\<rceil>\<^sub>S\<^sub><])"
  by (rel_auto)

lemma circus_alpha_bij_lens:
  "bij_lens ({$ok,$ok\<acute>,$wait,$wait\<acute>,$tr,$tr\<acute>,$st,$st\<acute>,$rref,$rref\<acute>}\<^sub>\<alpha> :: _ \<Longrightarrow> ('s,'e) rcsp_vars \<times> ('s,'e) rcsp_vars)"
  by (unfold_locales, lens_simp+)

subsection \<open> Unrestriction laws \<close>

lemma pre_unrest_ref [unrest]: "$rref \<sharp> P \<Longrightarrow> $rref \<sharp> pre\<^sub>R(P)"
  by (simp add: pre\<^sub>R_def unrest)

lemma peri_unrest_ref [unrest]: "$rref \<sharp> P \<Longrightarrow> $rref \<sharp> peri\<^sub>R(P)"
  by (simp add: peri\<^sub>R_def unrest)

lemma post_unrest_ref [unrest]: "$rref \<sharp> P \<Longrightarrow> $rref \<sharp> post\<^sub>R(P)"
  by (simp add: post\<^sub>R_def unrest)

lemma cmt_unrest_ref [unrest]: "$rref \<sharp> P \<Longrightarrow> $rref \<sharp> cmt\<^sub>R(P)"
  by (simp add: cmt\<^sub>R_def unrest)

lemma st_lift_unrest_ref' [unrest]: "$rref\<acute> \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)

lemma RHS_design_ref_unrest [unrest]:
  "\<lbrakk>$rref \<sharp> P; $rref \<sharp> Q \<rbrakk> \<Longrightarrow> $rref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q))\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma R1_ref_unrest [unrest]: "$rref \<sharp> P \<Longrightarrow> $rref \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref_unrest [unrest]: "$rref \<sharp> P \<Longrightarrow> $rref \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R1_ref'_unrest [unrest]: "$rref\<acute> \<sharp> P \<Longrightarrow> $rref\<acute> \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref'_unrest [unrest]: "$rref\<acute> \<sharp> P \<Longrightarrow> $rref\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R2s_notin_rref': "R2s(\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sup>\<R> $rref\<acute>) = (\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sup>\<R> $rref\<acute>)"
  by (pred_auto)

lemma unrest_circus_alpha:
  fixes P :: "('e, 't) raction"
  assumes 
    "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "$tr \<sharp> P" 
    "$tr\<acute> \<sharp> P" "$st \<sharp> P" "$st\<acute> \<sharp> P" "$rref \<sharp> P" "$rref\<acute> \<sharp> P"
  shows "\<Sigma> \<sharp> P"
  by (rule bij_lens_unrest_all[OF circus_alpha_bij_lens], simp add: unrest assms)

lemma unrest_all_circus_vars:
  fixes P :: "('s, 'e) raction"
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "$rref \<sharp> P" "\<Sigma> \<sharp> r'" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> s'" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "\<Sigma> \<sharp> [$rref\<acute> \<mapsto>\<^sub>s r', $st \<mapsto>\<^sub>s s, $st\<acute> \<mapsto>\<^sub>s s', $tr \<mapsto>\<^sub>s t, $tr\<acute> \<mapsto>\<^sub>s t'] \<dagger> P"
  using assms
  by (simp add: bij_lens_unrest_all_eq[OF circus_alpha_bij_lens] unrest_plus_split plus_vwb_lens)
     (simp add: unrest usubst closure)

lemma unrest_all_circus_vars_st_st':
  fixes P :: "('s, 'e) raction"
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "$rref \<sharp> P" "$rref\<acute> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> s'" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "\<Sigma> \<sharp> [$st \<mapsto>\<^sub>s s, $st\<acute> \<mapsto>\<^sub>s s', $tr \<mapsto>\<^sub>s t, $tr\<acute> \<mapsto>\<^sub>s t'] \<dagger> P"
  using assms
  by (simp add: bij_lens_unrest_all_eq[OF circus_alpha_bij_lens] unrest_plus_split plus_vwb_lens)
     (simp add: unrest usubst closure)

lemma unrest_all_circus_vars_st:
  fixes P :: "('s, 'e) raction"
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "$rref \<sharp> P" "$rref\<acute> \<sharp> P" "$st\<acute> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "\<Sigma> \<sharp> [$st \<mapsto>\<^sub>s s, $tr \<mapsto>\<^sub>s t, $tr\<acute> \<mapsto>\<^sub>s t'] \<dagger> P"
  using assms
  by (simp add: bij_lens_unrest_all_eq[OF circus_alpha_bij_lens] unrest_plus_split plus_vwb_lens)
      (simp add: unrest usubst closure)

lemma unrest_any_circus_var:
  fixes P :: "('s, 'e) raction"
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "$rref \<sharp> P" "$rref\<acute> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> s'" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "x \<sharp> [$st \<mapsto>\<^sub>s s, $st\<acute> \<mapsto>\<^sub>s s', $tr \<mapsto>\<^sub>s t, $tr\<acute> \<mapsto>\<^sub>s t'] \<dagger> P" 
  by (simp add: unrest_all_var unrest_all_circus_vars_st_st' assms)

lemma unrest_any_circus_var_st:
  fixes P :: "('s, 'e) raction"
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "$rref \<sharp> P" "$rref\<acute> \<sharp> P" "$st\<acute> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "x \<sharp> [$st \<mapsto>\<^sub>s s, $tr \<mapsto>\<^sub>s t, $tr\<acute> \<mapsto>\<^sub>s t'] \<dagger> P"
  by (simp add: unrest_all_var unrest_all_circus_vars_st assms)

subsection \<open> Basic Actions \<close>


lemma rref_closure_1 [closure]: "($tr\<acute> =\<^sub>u $tr \<and> $rref\<acute> =\<^sub>u \<guillemotleft>\<bullet>\<guillemotright>) is RR"
  apply (rel_auto)
  by (simp add: zero_list_def)

lemma rref_closure_2 [closure]: "$tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st is RR"
  apply (rel_auto)
  using minus_zero_eq by blast

lemma rref_closure_3 [closure]: "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sup>\<R> $rref\<acute>) is RR"
  by (rel_auto, simp add: zero_list_def)
  
lemma rref_closure_4 [closure]: "(\<^bold>\<exists> e \<bullet> U($tr\<acute> = $tr @ [\<guillemotleft>e\<guillemotright>] \<and> \<guillemotleft>revent(e)\<guillemotright> = \<lceil>a\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) is RR"
  by (rel_auto)

lemma rref_closure_5 [closure]: "(\<^bold>\<exists> e \<bullet> U($tr\<acute> = $tr @ [\<guillemotleft>e\<guillemotright>] \<and> \<guillemotleft>revent(e)\<guillemotright> = \<lceil>a\<rceil>\<^sub>S\<^sub>< \<and> $rref\<acute> = \<guillemotleft>\<bullet>\<guillemotright>)) is RR"
  by (rel_auto)

definition Stop :: "('s, 'e) raction" where
[upred_defs, rdes_def]: "Stop = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> ($tr\<acute> =\<^sub>u $tr) \<diamondop> false)"

definition Skip :: "('s, 'e) raction" where
[upred_defs, rdes_def]: "Skip = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr \<and> $rref\<acute> = \<bullet>) \<diamondop> U($tr\<acute> = $tr \<and> $st\<acute> = $st))"

definition Do :: "('e, 's) uexpr \<Rightarrow> ('s, 'e) raction" where
[upred_defs, rdes_def]: 
"Do(a) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (U($tr\<acute> = $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sup>\<R> $rref\<acute>) \<or> U(\<exists> e. $tr\<acute> = $tr @ [\<guillemotleft>e\<guillemotright>] \<and> \<guillemotleft>revent(e)\<guillemotright> = \<lceil>a\<rceil>\<^sub>S\<^sub>< \<and> $rref\<acute> = \<bullet>))
                  \<diamondop> U(\<exists> e. $tr\<acute> = $tr @ [\<guillemotleft>e\<guillemotright>] \<and> \<guillemotleft>revent(e)\<guillemotright> = \<lceil>a\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st))"

lemma "Skip ;; Stop = Stop"
  by (rdes_eq)

lemma "Skip ;; Chaos = Chaos"
  apply (rdes_eq_split)
    apply (rel_auto)
  oops -- {* Not true *}

lemma "Stop ;; Skip = Stop"
  by (rdes_eq)

lemma "Skip ;; Do(a) = Do(a)"
  by (rdes_eq)

lemma "Do(a) ;; Skip = Do(a)"
  by (rdes_eq)

lemma "Stop ;; Do(a) = Stop"
  by (rdes_eq)

term UINF

definition ResolveR :: "'a set \<Rightarrow> ('a \<Rightarrow> ('s, 'e) raction) \<Rightarrow> ('a \<Rightarrow> ('s, 'e) raction) \<Rightarrow> ('s, 'e) raction" where
"ResolveR A P Q = (\<^bold>\<exists> (e, t) \<bullet> (\<Or> i\<in>A \<bullet> ((P i)\<lbrakk>\<langle>\<rangle>,(\<langle>\<guillemotleft>e\<guillemotright>\<rangle>^\<^sub>u\<guillemotleft>t\<guillemotright>)/$tr,$tr\<acute>\<rbrakk>)) 
                          \<and> (\<And> i\<in>A \<bullet> ((Q i)\<lbrakk>\<langle>\<rangle>,\<langle>\<rangle>,\<guillemotleft>rrefusal(e)\<guillemotright>/$tr,$tr\<acute>,$rref\<acute>\<rbrakk>))
                          \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>t\<guillemotright>)"

syntax
  "_ResolveR" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("resolve _ \<in> _ \<bullet> '(_, _')" [0, 10] 10)

translations
  "resolve x \<in> A \<bullet> (F, G)" => "CONST ResolveR A (\<lambda> x. F) (\<lambda> x. G)"

definition 
  "ExtChoice A P = \<^bold>R\<^sub>s((\<And> i\<in>A \<bullet> pre\<^sub>R(P i)) \<turnstile> 
                      (R5(\<And> i\<in>A \<bullet> peri\<^sub>R(P(i))) \<or> (resolve i\<in>A \<bullet> (peri\<^sub>R(P(i)), peri\<^sub>R(P(i))))) \<diamondop> 
                      (R5(\<Or> i\<in>A \<bullet> post\<^sub>R(P(i))) \<and> (resolve i\<in>A \<bullet> (peri\<^sub>R(P(i)), post\<^sub>R(P(i))))))"

lemma "ExtChoice {} P = Stop"
  by (simp add: ExtChoice_def ResolveR_def rpred, rel_auto)


end