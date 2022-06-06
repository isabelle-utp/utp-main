section {* Relational Refinement Calculus *}

theory utp_morgan
  imports utp_hoare
begin
  
definition spec :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha> upred) \<Rightarrow> '\<alpha> hrel" where
[upred_defs]: "spec x p q = (\<Squnion> v \<bullet> \<lceil>p \<and> &\<^bold>v =\<^sub>u \<guillemotleft>v\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> x:[\<lceil>q(v)\<rceil>\<^sub>>])"

syntax
  "_init_var"  :: "logic"
  "_spec"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,/ _]" [99,0,0] 100)
  "_log_const" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("con _ \<bullet> _" [0, 10] 10)
  
translations
  "_spec x p q" => "CONST spec x p (\<lambda> _init_var. q)"
  "_spec (_salphaset (_salphamk x)) p q" <= "CONST spec x p (\<lambda> iv. q)"
  "_log_const x P" => "\<Squnion> x \<bullet> P"
  
parse_translation {*
let
  fun init_var_tr [] = Syntax.free "iv"
    | init_var_tr _  = raise Match;
in
[(@{syntax_const "_init_var"}, K init_var_tr)]
end
*}
  
lemma spec_simple_def: 
  "x:[pre,post] = (\<lceil>pre\<rceil>\<^sub>< \<Rightarrow> x:[\<lceil>post\<rceil>\<^sub>>])"
  by (rel_auto)
  
lemma spec_abort:
  "x:[false,post] = true"
  by (rel_auto)
 
lemma spec_skip:
  "\<emptyset>:[true,true] = II"
  by (rel_auto)
    
lemma assign_refine:
  assumes "vwb_lens w" "vwb_lens x" "w \<bowtie> x" "`pre \<Rightarrow> post\<lbrakk>E/w\<rbrakk>`"
  shows "{&w,&x}:[pre,post] \<sqsubseteq> w := E"
  apply (insert assms)
  apply (rel_simp)
  apply (metis lens_indep.lens_put_irr2 lens_override_def lens_override_idem vwb_lens_wb wb_lens_def weak_lens.put_get)
done
    
lemma seqr_refine:
  "\<lbrakk> vwb_lens w; w \<natural> mid \<rbrakk> \<Longrightarrow> w:[pre,post] \<sqsubseteq> w:[pre,mid] ;; w:[mid,post]"  
  by (rel_simp)
   
lemma log_const_intro:
  assumes "vwb_lens w" "`pre \<Rightarrow> (\<^bold>\<exists> c \<bullet> pre'(c))`"
  shows "w:[pre,post] \<sqsubseteq> (con c \<bullet> w:[pre'(c),post])"
  apply (insert assms)
  apply (rel_blast)
done
    
lemma log_const_initial:
  assumes "vwb_lens w"
  shows "w:[pre,post] \<sqsubseteq> (con c \<bullet> w:[pre \<and> \<guillemotleft>c\<guillemotright> =\<^sub>u E, post])"
  using assms by (rule log_const_intro, rel_auto)
    
lemma log_const_remove:
  assumes "vwb_lens w"
  shows "(con c \<bullet> w:[pre,post]) \<sqsubseteq> w:[pre,post]"
  by (rel_auto)
    
syntax
  "_ulens_expr" :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("_:'(_')" [100,100] 100)

translations
  "_ulens_expr e x" == "CONST uop get\<^bsub>x\<^esub> e"
  
lemma expand_frame:
  assumes "vwb_lens w" "vwb_lens x" "x \<bowtie> w" "w \<natural> post"
  shows "{&w}:[true,post] = {&w,&x}:[true, post \<and> &x =\<^sub>u \<guillemotleft>iv\<guillemotright>:(x)]"
  apply (simp add: spec_def)
  using assms apply (rel_auto)
  apply fastforce
done  
    
end