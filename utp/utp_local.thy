theory utp_local
imports utp_rel
begin

type_synonym ('a, '\<alpha>) lvar = "('a list, '\<alpha>) uvar"

lift_definition xex :: "('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<exists> v. P (put\<^bsub>x\<^esub> b (v # get\<^bsub>x\<^esub> b)))" .

syntax
  "_xex" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<exists>\<^sub>+ _ \<bullet> _" [0, 10] 10)

translations
  "_xex x P" == "CONST xex x P"

definition var_begin :: "('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> hrelation" ("var _" [100] 100) where
[urel_defs]: "var_begin x = (\<exists>\<^sub>+ $x \<bullet> II)"

definition var_end :: "('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> hrelation" ("end _" [100] 100) where
[urel_defs]: "var_end x = (\<exists>\<^sub>+ $x\<acute> \<bullet> II)"

text {* The variable at the top of the local variable stack *}

definition top_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a, '\<alpha>) uvar" where
[upred_defs]: "top_var x = (list_lens 0 ;\<^sub>L x)"

text {* The remainder of the local variable stack (the tail) *}

definition rest_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a list, '\<alpha>) uvar" where
[upred_defs]: "rest_var x = (tl_lens ;\<^sub>L x)"

text {* The top most variable is independent of the rest of the stack *}

lemma top_rest_var_indep [simp]:  
  "uvar x \<Longrightarrow> top_var x \<bowtie> rest_var x"
  by (simp add: lens_indep_left_comp rest_var_def top_var_def)

syntax
  "_top_var"      :: "id \<Rightarrow> svid" ("@_" [999] 999)
  "_rest_var"     :: "id \<Rightarrow> svid" ("\<down>_" [999] 999)
  "_var_scope"    :: "id \<Rightarrow> logic \<Rightarrow> logic" ("var _ \<bullet> _" [0,10] 10)
  "_var_scope_ty" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ : _ \<bullet> _" [0,0,10] 10)

translations
  "_top_var x" == "CONST top_var x"
  "_rest_var x" == "CONST rest_var x"
  "var x \<bullet> P" => "var x ;; ((\<lambda> x. P) (CONST top_var x)) ;; end x"
  "var x : 'a \<bullet> P" => "var x ;; ((\<lambda> x :: ('a, _) uvar. P) (CONST top_var x)) ;; end x"

lemma var_open_end:
  "uvar x \<Longrightarrow> (var x ;; end x) = II"
  by (rel_tac, metis list.inject mwb_lens_weak vwb_lens.put_eq vwb_lens_mwb weak_lens.view_determination, blast)
  
lemma var_open_close_commute:
  assumes "uvar x" "uvar y" "x \<bowtie> y"
  shows "(var x ;; end y) = (end y ;; var x)"
  using assms
  apply (rel_tac)
  apply (smt lens_indep_comm vwb_lens.put_eq vwb_lens_wb wb_lens_def weak_lens.put_get)
  apply (metis lens_indep_def)
done
  
lemma var_block_vacuous: 
  "uvar x \<Longrightarrow> (var x \<bullet> II) = II"
  by (simp add: var_open_end)

end