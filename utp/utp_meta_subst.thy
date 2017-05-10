section {* Meta-level substitution *}

theory utp_meta_subst
imports utp_rel
begin
  
definition msubst :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> '\<alpha> upred" where
[upred_defs]: "msubst F v = (\<Sqinter> x | \<guillemotleft>x\<guillemotright> =\<^sub>u v \<bullet> F(x))"

syntax
  "_msubst"   :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("(_\<lbrakk>_\<rightarrow>_\<rbrakk>)" [990,0,0] 991)

translations
  "_msubst P x v" => "CONST msubst (\<lambda> x. P) v"
 
lemma msubst_true [usubst]: "true\<lbrakk>x\<rightarrow>v\<rbrakk> = true"
  by (pred_auto)

lemma msubst_false [usubst]: "false\<lbrakk>x\<rightarrow>v\<rbrakk> = false"
  by (pred_auto)
    
lemma msubst_lit [usubst]: "\<guillemotleft>x\<guillemotright>\<lbrakk>x\<rightarrow>v\<rbrakk> = v"
  by (pred_auto)

lemma msubst_not [usubst]: "(\<not> P(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = (\<not> ((P x)\<lbrakk>x\<rightarrow>v\<rbrakk>))"
  by (pred_auto)
    
lemma msubst_disj [usubst]: "(P(x) \<or> Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = ((P(x))\<lbrakk>x\<rightarrow>v\<rbrakk> \<or> (Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (pred_auto)
    
lemma msubst_conj [usubst]: "(P(x) \<and> Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = ((P(x))\<lbrakk>x\<rightarrow>v\<rbrakk> \<and> (Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (pred_auto)
  
lemma msubst_seq [usubst]: "(P(x) ;; Q(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk> = ((P(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk> ;; (Q(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk>)"
  by (rel_auto)  
    
lemma msubst_unrest [unrest]: "\<lbrakk> \<And> v. x \<sharp> P(v); x \<sharp> k \<rbrakk> \<Longrightarrow> x \<sharp> P(v)\<lbrakk>v\<rightarrow>k\<rbrakk>"
  by (pred_auto)
  
end