section \<open> Stateful-Failure Reactive Contracts \<close>

theory utp_sfrd_contracts
  imports utp_sfrd_healths
begin

definition mk_CRD :: "'s upred \<Rightarrow> ('e list \<Rightarrow> 'e set \<Rightarrow> 's upred) \<Rightarrow> ('e list \<Rightarrow> 's hrel) \<Rightarrow> ('s, 'e) action" where
[rdes_def]: "mk_CRD P Q R = \<^bold>R\<^sub>s([P]\<^sub>S\<^sub>< \<turnstile> [Q x r]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> \<diamondop> [R(x)]\<^sub>S'\<lbrakk>x\<rightarrow>&tt\<rbrakk>)"

syntax
  "_ref_var" :: "logic"
  "_mk_CRD"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("[_/ \<turnstile> _/ | _]\<^sub>C")

parse_translation \<open>
let
  fun ref_var_tr [] = Syntax.free "refs"
    | ref_var_tr _  = raise Match;
in
[(@{syntax_const "_ref_var"}, K ref_var_tr)]
end
\<close>

translations
  "_mk_CRD P Q R" => "CONST mk_CRD P (\<lambda> _trace_var _ref_var. Q) (\<lambda> _trace_var. R)"
  "_mk_CRD P Q R" <= "CONST mk_CRD P (\<lambda> x r. Q) (\<lambda> y. R)"

lemma CSP_mk_CRD [closure]: "[P \<turnstile> Q trace refs | R(trace)]\<^sub>C is CSP"
  by (simp add: mk_CRD_def closure unrest)

lemma preR_mk_CRD [rdes]: "pre\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = [P]\<^sub>S\<^sub><"
  by (simp add: mk_CRD_def rea_pre_RHS_design usubst unrest R2c_not R2c_lift_state_pre rea_st_cond_def, rel_auto)

lemma periR_mk_CRD [rdes]: "peri\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = ([P]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r ([Q trace refs]\<^sub>S\<^sub><)\<lbrakk>(trace,refs)\<rightarrow>(&tt,$ref\<acute>)\<^sub>u\<rbrakk>)"
  by (simp add: mk_CRD_def rea_peri_RHS_design usubst unrest R2c_not R2c_lift_state_pre
                impl_alt_def R2c_disj R2c_msubst_tt R1_disj, rel_auto)

lemma postR_mk_CRD [rdes]: "post\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = ([P]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r ([R(trace)]\<^sub>S')\<lbrakk>trace\<rightarrow>&tt\<rbrakk>)"
  by (simp add: mk_CRD_def rea_post_RHS_design usubst unrest R2c_not R2c_lift_state_pre
                impl_alt_def R2c_disj R2c_msubst_tt R1_disj, rel_auto)

text \<open> Refinement introduction law for contracts \<close>

lemma CRD_contract_refine:
  assumes
    "Q is CSP" "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R Q`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>2 t r\<rceil>\<^sub>S\<^sub><\<lbrakk>t\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk>`"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> Q"
proof -
  have "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    using assms by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, rel_auto+)
  thus ?thesis
    by (simp add: SRD_reactive_tri_design assms(1))
qed

lemma CRD_contract_refine':
  assumes
    "Q is CSP" "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R Q`"
    "\<lceil>P\<^sub>2 t r\<rceil>\<^sub>S\<^sub><\<lbrakk>t\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R Q)"
    "\<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R Q)"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> Q"
  using assms by (rule_tac CRD_contract_refine, simp_all add: refBy_order)
  
lemma CRD_refine_CRD: 
  assumes 
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> (\<lceil>Q\<^sub>1\<rceil>\<^sub>S\<^sub>< :: ('e,'s) action)`"
    "(\<lceil>P\<^sub>2 x r\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>Q\<^sub>2 x r\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> :: ('e,'s) action)"
    "\<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>Q\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> :: ('e,'s) action)"
  shows "([P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3 trace]\<^sub>C :: ('e,'s) action) \<sqsubseteq> [Q\<^sub>1 \<turnstile> Q\<^sub>2 trace refs | Q\<^sub>3 trace]\<^sub>C"
  using assms
  by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, rel_auto+)

lemma CRD_refine_rdes: 
  assumes 
    "`[P\<^sub>1]\<^sub>S\<^sub>< \<Rightarrow> Q\<^sub>1`"
    "([P\<^sub>2 x r]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>2)"
    "[P\<^sub>3 x]\<^sub>S'\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>3)"
  shows "([P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3 trace]\<^sub>C :: ('e,'s) action) \<sqsubseteq> 
          \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  using assms
  by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, rel_auto+)

lemma CRD_refine_rdes': 
  assumes
    "Q\<^sub>2 is RR"
    "Q\<^sub>3 is RR"
    "`[P\<^sub>1]\<^sub>S\<^sub>< \<Rightarrow> Q\<^sub>1`"
    "\<And> t. ([P\<^sub>2 t r]\<^sub>S\<^sub><\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>2\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)"
    "\<And> t. [P\<^sub>3 t]\<^sub>S' \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>3\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)"
  shows "([P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3 trace]\<^sub>C :: ('e,'s) action) \<sqsubseteq> 
          \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
proof (simp add: mk_CRD_def, rule srdes_tri_refine_intro)
  show "`[P\<^sub>1]\<^sub>S\<^sub>< \<Rightarrow> Q\<^sub>1`" by (fact assms(3))

  have "\<And> t. ([P\<^sub>2 t r]\<^sub>S\<^sub><\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> (RR Q\<^sub>2)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)"
    by (simp add: assms Healthy_if)
  hence "`[P\<^sub>1]\<^sub>S\<^sub>< \<and> RR(Q\<^sub>2) \<Rightarrow> [P\<^sub>2 x r]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>`"
    by (rel_simp; meson)
  thus "`[P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>2 \<Rightarrow> [P\<^sub>2 x r]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>`"
    by (simp add: Healthy_if assms)

  have "\<And> t. [P\<^sub>3 t]\<^sub>S' \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> (RR Q\<^sub>3)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)"
    by (simp add: assms Healthy_if)
  hence "`[P\<^sub>1]\<^sub>S\<^sub>< \<and> (RR Q\<^sub>3) \<Rightarrow> [P\<^sub>3 x]\<^sub>S'\<lbrakk>x\<rightarrow>&tt\<rbrakk>`"
    by (rel_simp; meson)
  thus "`[P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>3 \<Rightarrow> [P\<^sub>3 x]\<^sub>S'\<lbrakk>x\<rightarrow>&tt\<rbrakk>`"
    by (simp add: Healthy_if assms)
qed

end