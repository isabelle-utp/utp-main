header {* Set by Characteristic Function *}
theory Impl_Cfun_Set
imports "../Intf/Intf_Set"
begin

definition fun_set_rel where
  fun_set_rel_internal_def: 
  "fun_set_rel R \<equiv> (R\<rightarrow>bool_rel) O br Collect (\<lambda>_. True)"

lemma fun_set_rel_def: "\<langle>R\<rangle>fun_set_rel = (R\<rightarrow>bool_rel) O br Collect (\<lambda>_. True)"
  by (simp add: relAPP_def fun_set_rel_internal_def)

lemma fun_set_rel_sv[relator_props]: 
  "\<lbrakk>single_valued R; Range R = UNIV\<rbrakk> \<Longrightarrow> single_valued (\<langle>R\<rangle>fun_set_rel)"
  unfolding fun_set_rel_def
  by (tagged_solver (keep))

lemmas [autoref_rel_intf] = REL_INTFI[of fun_set_rel i_set]

lemma fs_mem_refine[autoref_rules]: "(\<lambda>x f. f x,op \<in>) \<in> R \<rightarrow> \<langle>R\<rangle>fun_set_rel \<rightarrow> bool_rel"
  apply (intro fun_relI)
  apply (auto simp add: fun_set_rel_def br_def dest: fun_relD)
  done
end
