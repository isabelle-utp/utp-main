theory utp_local
imports utp_rel Char_ord
begin

type_synonym ('a, '\<alpha>) lvar = "('a list, '\<alpha>) uvar"

lift_definition xex :: "('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<exists> v. P (put\<^bsub>x\<^esub> b (v # get\<^bsub>x\<^esub> b)))" .

syntax
  "_xex" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<exists>\<^sub>+ _ \<bullet> _" [0, 10] 10)

translations
  "_xex x P" == "CONST xex x P"

definition var_begin :: "('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "var_begin x = (\<exists>\<^sub>+ $x \<bullet> II)"

definition var_end :: "('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "var_end x = (\<exists>\<^sub>+ $x\<acute> \<bullet> II)"

text {* vlet ensures that there is a variable on the top of the stack *}

definition var_vlet :: "('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "var_vlet x = (($x \<noteq>\<^sub>u \<langle>\<rangle>) \<and> II)"

syntax
  "_var_begin"  :: "svid \<Rightarrow> logic" ("var _" [100] 100)
  "_var_end"    :: "svid \<Rightarrow> logic" ("end _" [100] 100)
  "_var_vlet" :: "svid \<Rightarrow> logic" ("vlet _" [100] 100)

translations
  "_var_begin x" == "CONST var_begin x"
  "_var_end x" == "CONST var_end x"
  "_var_vlet x" == "CONST var_vlet x"

text {* The variable at the top of the local variable stack *}

definition top_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a, '\<alpha>) uvar" where
[upred_defs]: "top_var x = (list_lens 0 ;\<^sub>L x)"

text {* The remainder of the local variable stack (the tail) *}

definition rest_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a list, '\<alpha>) uvar" where
[upred_defs]: "rest_var x = (tl_lens ;\<^sub>L x)"

text {* The top most variable is independent of the rest of the stack *}

lemma top_semi_uvar [simp]: "uvar x \<Longrightarrow> semi_uvar (top_var x)"
  by (simp add: list_mwb_lens top_var_def)

lemma top_rest_var_indep [simp]:  
  "uvar x \<Longrightarrow> top_var x \<bowtie> rest_var x"
  by (simp add: lens_indep_left_comp rest_var_def top_var_def)

lemma top_var_pres_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> top_var x \<bowtie> y"
  by (simp add: lens_indep_left_ext top_var_def)

syntax
  "_top_var"             :: "svid \<Rightarrow> svid" ("@_" [999] 999)
  "_rest_var"            :: "svid \<Rightarrow> svid" ("\<down>_" [999] 999)
  "_var_scope"           :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("var _ \<bullet> _" [0,10] 10)
  "_var_scope_ty"        :: "svid \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ :: _ \<bullet> _" [0,0,10] 10)
  "_var_scope_ty_assign" :: "svid \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("var _ :: _ := _ \<bullet> _" [0,0,0,10] 10)

translations
  "_top_var x" == "CONST top_var x"
  "_rest_var x" == "CONST rest_var x"
  "var x \<bullet> P" => "var x ;; ((\<lambda> x. P) (CONST top_var x)) ;; end x"
  "var \<guillemotleft>x\<guillemotright> \<bullet> P" => "var \<guillemotleft>x\<guillemotright> ;; ((\<lambda> x. P) (CONST top_var (CONST MkDVar IDSTR(x)))) ;; end \<guillemotleft>x\<guillemotright>"
  "var \<guillemotleft>x\<guillemotright> :: 'a \<bullet> P" => "var \<guillemotleft>x::'a list\<guillemotright> ;; ((\<lambda> x :: ('a, _) uvar. P) (CONST top_var (CONST MkDVar IDSTR(x)))) ;; end \<guillemotleft>x::'a list\<guillemotright>"
  "var \<guillemotleft>x\<guillemotright>  :: 'a := v \<bullet> P" => "var \<guillemotleft>x\<guillemotright> :: 'a \<bullet> x := v ;; P"

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

lemma assign_var_end: "uvar x \<Longrightarrow> (vlet x ;; @x := v ;; end x) = end x"
  apply (rel_tac)
  apply (metis list_augment_0 mwb_lens_weak neq_Nil_conv vwb_lens.put_eq vwb_lens_mwb weak_lens.view_determination)
  apply (auto)
done

lemma var_open_alt_def: "var x = (\<^bold>\<exists> v \<bullet> x := \<langle>\<guillemotleft>v\<guillemotright>\<rangle> ^\<^sub>u &x)"
  by (rel_tac)

lemma var_close_alt_def: "uvar x \<Longrightarrow> end x = (x := tail\<^sub>u(&x) \<triangleleft> $x \<noteq>\<^sub>u \<langle>\<rangle> \<triangleright> false)"
  apply (rel_tac)
  apply (metis hd_Cons_tl vwb_lens.put_eq)
done
  
lemma var_open_refine: "var x \<sqsubseteq> x := \<langle>\<guillemotleft>v\<guillemotright>\<rangle> ^\<^sub>u &x"
  by (rel_tac)

lemma var_open_vlet: "uvar x \<Longrightarrow> (var x ;; vlet x) = var x"
  by (rel_tac)

lemma var_block_assign: "uvar x \<Longrightarrow> (var x \<bullet> x := v) = II"
  apply (rel_tac)
  apply (metis list.inject mwb_lens_weak vwb_lens.put_eq vwb_lens_mwb weak_lens.view_determination)
  apply force
done

lemma var_block_assigns: "\<lbrakk> uvar x; &x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> (var x \<bullet> \<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>a) = \<langle>\<sigma>\<rangle>\<^sub>a"
  apply (rel_tac)
  apply (auto simp add: comp_def unrest_usubst_def)
  apply (metis (no_types, lifting) list.inject mwb_lens_weak vwb_lens.put_eq vwb_lens_mwb weak_lens.view_determination)
  apply (metis list_augment_0 mwb_lens.put_put mwb_lens_weak vwb_lens_mwb vwb_lens_wb wb_lens.get_put weak_lens.put_get)
done

text {* Example of "deep" variable blocks *}

lemma "(var \<guillemotleft>x\<guillemotright> :: int \<bullet> (x := 1 ;; \<guillemotleft>y::int\<guillemotright> := &x + 2)) = \<guillemotleft>y::int\<guillemotright> := 3"
  apply (subst assign_r_comp)
  apply (simp add: usubst unrest)
  apply (subst assign_subst)
  apply (simp)
  apply (simp)
  apply (simp add: usubst unrest)
  apply (subst usubst_upd_comm)
  apply (simp)
  apply (subst var_block_assigns)
  apply (simp)
  apply (simp add: unrest)
  apply (simp)
done

end