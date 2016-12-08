subsection {* Variable blocks *}

theory utp_local
imports utp_theory utp_designs
begin

type_synonym ('a, '\<alpha>) lvar = "('a list, '\<alpha>) uvar"

consts 
  pvar         :: "'\<beta> \<Longrightarrow> '\<alpha>" ("\<^bold>v")
  pvar_assigns :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> '\<beta> usubst \<Rightarrow> '\<alpha> hrelation" ("\<^bold>\<langle>_\<^bold>\<rangle>\<index>")

syntax
  "_svid_pvar" :: "svid" ("\<^bold>v")
  "_thy_asgn"  :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> svid_list \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr "::=\<index>" 55)

translations
  "_svid_pvar" => "CONST pvar"
  "_thy_asgn T xs vs" => "CONST pvar_assigns T (_mk_usubst (CONST id) xs vs)"

text {* The variable at the top of the local variable stack *}

definition top_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a, '\<alpha>) uvar" where
[upred_defs]: "top_var x = (list_lens 0 ;\<^sub>L x)"

text {* The remainder of the local variable stack (the tail) *}

definition rest_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a list, '\<alpha>) uvar" where
[upred_defs]: "rest_var x = (tl_lens ;\<^sub>L x)"

text {* The top most variable is independent of the rest of the stack *}

lemma top_mwb_lens [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (top_var x)"
  by (simp add: list_mwb_lens top_var_def)

lemma top_rest_var_indep [simp]:  
  "mwb_lens x \<Longrightarrow> top_var x \<bowtie> rest_var x"
  by (simp add: lens_indep_left_comp rest_var_def top_var_def)

lemma top_var_pres_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> top_var x \<bowtie> y"
  by (simp add: lens_indep_left_ext top_var_def)

syntax
  "_top_var"             :: "svid \<Rightarrow> svid" ("@_" [999] 999)
  "_rest_var"            :: "svid \<Rightarrow> svid" ("\<down>_" [999] 999)

translations
  "_top_var x" == "CONST top_var x"
  "_rest_var x" == "CONST rest_var x"


definition var_begin :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> ('a, '\<beta>) lvar \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "var_begin T x = x ::=\<^bsub>T\<^esub> \<langle>\<guillemotleft>undefined\<guillemotright>\<rangle> ^\<^sub>u &x"

definition var_end :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> ('a, '\<beta>) lvar \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "var_end T x = (x ::=\<^bsub>T\<^esub> tail\<^sub>u(&x))"

definition var_vlet :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> ('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "var_vlet T x = (($x \<noteq>\<^sub>u \<langle>\<rangle>) \<and> \<I>\<I>\<^bsub>T\<^esub>)"

syntax
  "_var_begin"     :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("var\<index> _" [100] 100)
  "_var_begin_asn" :: "logic \<Rightarrow> svid \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ := _")
  "_var_end"       :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("end\<index> _" [100] 100)
  "_var_vlet"      :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("vlet\<index> _" [100] 100)
  "_var_scope"           :: "logic \<Rightarrow> svid \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ \<bullet> _" [0,10] 10)
  "_var_scope_ty"        :: "logic \<Rightarrow> svid \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ :: _ \<bullet> _" [0,0,10] 10)
  "_var_scope_ty_assign" :: "logic \<Rightarrow> svid \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ :: _ := _ \<bullet> _" [0,0,0,10] 10)

translations
  "_var_begin T x"       == "CONST var_begin T x"
  "_var_begin_asn T x e" => "var\<^bsub>T\<^esub> x ;; @x ::=\<^bsub>T\<^esub> e"
  "_var_end T x"         == "CONST var_end T x"
  "_var_vlet T x"        == "CONST var_vlet T x"
  "var\<^bsub>T\<^esub> x \<bullet> P" => "var\<^bsub>T\<^esub> x ;; ((\<lambda> x. P) (CONST top_var x)) ;; end\<^bsub>T\<^esub> x"
  "var\<^bsub>T\<^esub> x \<bullet> P" => "var\<^bsub>T\<^esub> x ;; ((\<lambda> x. P) (CONST top_var x)) ;; end\<^bsub>T\<^esub> x"
  "var\<^bsub>T\<^esub> <x> \<bullet> P" => "var\<^bsub>T\<^esub> <x> ;; ((\<lambda> x. P) (CONST top_var (CONST MkDVar IDSTR(x)))) ;; end\<^bsub>T\<^esub> <x>"
  "var\<^bsub>T\<^esub> <x> :: 'a \<bullet> P" => "var\<^bsub>T\<^esub> <x::'a list> ;; ((\<lambda> x :: ('a, _) uvar. P) (CONST top_var (CONST MkDVar IDSTR(x)))) ;; end\<^bsub>T\<^esub> <x::'a list>"
  "var\<^bsub>T\<^esub> <x>  :: 'a := v \<bullet> P" => "var\<^bsub>T\<^esub> <x> :: 'a \<bullet> x ::=\<^bsub>T\<^esub> v ;; P"

overloading
  des_pvar == "pvar :: '\<alpha> \<Longrightarrow> '\<alpha> alphabet_d"
  des_assigns == "pvar_assigns :: (DES \<times> '\<alpha> alphabet_d) itself \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrelation_d"
begin
  definition des_pvar :: "'\<alpha> \<Longrightarrow> '\<alpha> alphabet_d" where
  "des_pvar = \<Sigma>\<^sub>D"
  definition des_assigns :: "(DES \<times> '\<alpha> alphabet_d) itself \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrelation_d" where
  "des_assigns T \<sigma> = \<langle>\<sigma>\<rangle>\<^sub>D"
end

locale utp_prog_var = utp_theory \<T> for \<T> :: "('\<T> \<times> '\<alpha>) itself" (structure) +
  fixes \<V>\<T> :: "'\<beta>::vst itself"
  assumes pvar_uvar: "vwb_lens (\<^bold>v :: '\<beta> \<Longrightarrow> '\<alpha>)"
  and Healthy_pvar_assigns: "\<^bold>\<langle>\<sigma> :: '\<beta> usubst\<^bold>\<rangle> is \<H>"
  and pvar_assigns_comp: "(\<^bold>\<langle>\<sigma>\<^bold>\<rangle> ;; \<^bold>\<langle>\<rho>\<^bold>\<rangle>) = \<^bold>\<langle>\<rho> \<circ> \<sigma>\<^bold>\<rangle>"

lemma assigns_d_is_H1_H2:
  "\<langle>\<sigma>\<rangle>\<^sub>D is H1_H2"
  by (simp add: assigns_d_def rdesign_is_H1_H2) 

interpretation des_prog_var: utp_prog_var "TYPE(DES \<times> '\<alpha> alphabet_d)" "TYPE('\<alpha>::vst)"
  apply (unfold_locales, simp_all add: des_pvar_def des_assigns_def des_hcond_def)
  apply (simp add: assigns_d_def rdesign_is_H1_H2)
  apply (simp add: assigns_d_comp_ext assigns_d_is_H1_H2)
  apply (rel_auto)
done

locale utp_local_var = utp_prog_var \<T> V + utp_theory_left_unital \<T> for \<T> :: "('\<T> \<times> '\<alpha>) itself" (structure) and V :: "'\<beta>::vst itself" +
  assumes pvar_assign_unit: "\<^bold>\<langle>id :: '\<beta> usubst\<^bold>\<rangle> = \<I>\<I>"
begin

lemma var_begin_healthy: 
  fixes x :: "('a, '\<beta>) lvar"
  shows "var x is \<H>"
  by (simp add: var_begin_def Healthy_pvar_assigns)

lemma var_end_healthy: 
  fixes x :: "('a, '\<beta>) lvar"
  shows "end x is \<H>"
  by (simp add: var_end_def Healthy_pvar_assigns)

lemma var_open_close:
  fixes x :: "('a, '\<beta>) lvar"
  assumes "vwb_lens x"
  shows "(var x ;; end x) = \<I>\<I>"
  by (simp add: var_begin_def var_end_def shEx_lift_seq_1 Healthy_pvar_assigns pvar_assigns_comp pvar_assign_unit usubst assms)

lemma var_open_close_commute:
  fixes x :: "('a, '\<beta>) lvar" and y :: "('b, '\<beta>) lvar"
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "(var x ;; end y) = (end y ;; var x)"
  by (simp add: var_begin_def var_end_def shEx_lift_seq_1 shEx_lift_seq_2 
                Healthy_pvar_assigns pvar_assigns_comp
                assms usubst unrest  lens_indep_sym, simp add: assms usubst_upd_comm)

lemma var_block_vacuous: 
  fixes x :: "('a::two, '\<beta>) lvar"
  assumes "vwb_lens x"
  shows "(var x \<bullet> \<I>\<I>) = \<I>\<I>"
  by (simp add: Left_Unit assms var_end_healthy var_open_close)

end

interpretation des_local_var: utp_local_var "TYPE(DES \<times> '\<alpha> alphabet_d)" "TYPE('\<alpha>::vst)"
  by (unfold_locales, simp_all add: des_unit_def des_assigns_def)

(*
term "var\<^bsub>REL\<^esub> x \<bullet> P"

  
lemma var_open_close_commute:
  assumes "uvar x" "uvar y" "x \<bowtie> y"
  shows "(var x ;; end y) = (end y ;; var x)"
  using assms
  apply (rel_auto)
  apply (smt lens_indep_comm vwb_lens.put_eq vwb_lens_wb wb_lens_def weak_lens.put_get)
  apply (metis lens_indep_def)
done
  
lemma var_block_vacuous: 
  "uvar x \<Longrightarrow> (var x \<bullet> II) = II"
  by (simp add: var_open_end)

lemma assign_var_end: "uvar x \<Longrightarrow> (vlet x ;; @x := v ;; end x) = end x"
  apply (rel_auto)
  apply (metis list_augment_0 mwb_lens_weak neq_Nil_conv vwb_lens.put_eq vwb_lens_mwb weak_lens.view_determination)
  apply (auto)
done

lemma var_open_alt_def: "var x = (\<^bold>\<exists> v \<bullet> x := \<langle>\<guillemotleft>v\<guillemotright>\<rangle> ^\<^sub>u &x)"
  by (rel_auto)

lemma var_close_alt_def: "uvar x \<Longrightarrow> end x = (x := tail\<^sub>u(&x) \<triangleleft> $x \<noteq>\<^sub>u \<langle>\<rangle> \<triangleright> false)"
  apply (rel_auto)
  apply (metis hd_Cons_tl vwb_lens.put_eq)
done
  
lemma var_open_refine: "var x \<sqsubseteq> x := \<langle>\<guillemotleft>v\<guillemotright>\<rangle> ^\<^sub>u &x"
  by (rel_auto)

lemma var_open_vlet: "uvar x \<Longrightarrow> (var x ;; vlet x) = var x"
  by (rel_auto)

lemma var_RID_commute:
  "uvar x \<Longrightarrow> (var x ;; RID(x)(P)) = (RID(x)(P) ;; var x)"
  apply (rel_auto)
  apply (smt mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)
  apply (metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens_weak weak_lens.put_get)
done

lemma var_runrest_commute:
  "\<lbrakk> uvar x; x \<sharp>\<sharp> P \<rbrakk> \<Longrightarrow> (var x ;; P) = (P ;; var x)"
  by (metis unrest_relation_def var_RID_commute)

lemma end_RID_commute:
  "uvar x \<Longrightarrow> (RID(x)(P) ;; end x) = (end x ;; RID(x)(P))"
  apply (rel_auto)
  apply (smt vwb_lens.put_eq vwb_lens_wb wb_lens_weak weak_lens.put_get)
  apply (metis mwb_lens_axioms_def mwb_lens_def vwb_lens_mwb weak_lens.put_get)
done

lemma end_runrest_commute:
  "\<lbrakk> uvar x; x \<sharp>\<sharp> P \<rbrakk> \<Longrightarrow> (P ;; end x) = (end x ;; P)"
  by (metis end_RID_commute unrest_relation_def)

lemma var_block_collapse:
  "\<lbrakk> uvar x; x \<sharp>\<sharp> P \<rbrakk> \<Longrightarrow> (var x \<bullet> P) = P"
  by (simp add: end_runrest_commute seqr_assoc var_open_end)

lemma var_block_out_left:
  "\<lbrakk> uvar x; x \<sharp>\<sharp> P \<rbrakk> \<Longrightarrow> (var x \<bullet> P ;; Q x) = (P ;; (var x \<bullet> Q x))"
  by (simp add: seqr_assoc var_runrest_commute)

lemma var_block_out_right:
  "\<lbrakk> uvar x; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> (var x \<bullet> P x ;; Q) = ((var x \<bullet> P x) ;; Q)"
  by (metis end_runrest_commute seqr_assoc)

lemma var_block_assign: "uvar x \<Longrightarrow> (var x \<bullet> x := v) = II"
  apply (rel_auto)
  apply (metis list.inject mwb_lens_weak vwb_lens.put_eq vwb_lens_mwb weak_lens.view_determination)
  apply force
done

lemma var_block_assigns: "\<lbrakk> uvar x; &x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> (var x \<bullet> \<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>a) = \<langle>\<sigma>\<rangle>\<^sub>a"
  apply (rel_auto)
  apply (auto simp add: comp_def unrest_usubst_def)
  apply (metis (no_types, lifting) list.inject mwb_lens_weak vwb_lens.put_eq vwb_lens_mwb weak_lens.view_determination)
  apply (metis list_augment_0 mwb_lens.put_put mwb_lens_weak vwb_lens_mwb vwb_lens_wb wb_lens.get_put weak_lens.put_get)
done

text {* Example of "deep" variable blocks *}

lemma "(var <x> :: int \<bullet> (x := 1 ;; <y::int> := &x + 2)) = <y::int> := 3"
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
*)

end
