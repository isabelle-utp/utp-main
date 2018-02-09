section {* Syntax for reactive design contracts *}

theory utp_rdes_contracts
  imports utp_rdes_normal
begin

text {* We give an experimental syntax for reactive design contracts $[P \vdash Q | R]_R$, where $P$ is
  a precondition on undashed state variables only, $Q$ is a pericondition that can refer to the
  trace and before state but not the after state, and $R$ is a postcondition. Both $Q$ and $R$
  can refer only to the trace contribution through a HOL variable $trace$ which is bound to
  @{term "&tt"}. *}

definition mk_RD :: "'s upred \<Rightarrow> ('t::trace \<Rightarrow> 's upred) \<Rightarrow> ('t \<Rightarrow> 's hrel) \<Rightarrow> ('s, 't, 'a) hrel_rsp" where
"mk_RD P Q R = \<^bold>R\<^sub>s(\<lceil>P\<rceil>\<^sub>S\<^sub>< \<turnstile> \<lceil>Q(x)\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<diamondop> \<lceil>R(x)\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk>)"

definition trace_pred :: "('t::trace \<Rightarrow> 's upred) \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" where
[upred_defs]: "trace_pred P = [(P x)]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>"

syntax
  "_trace_var" :: "logic"
  "_mk_RD"    :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("[_/ \<turnstile> _/ | _]\<^sub>R")
  "_trace_pred"    :: "logic \<Rightarrow> logic" ("[_]\<^sub>t")

parse_translation {*
let
  fun trace_var_tr [] = Syntax.free "trace"
    | trace_var_tr _  = raise Match;
in
[(@{syntax_const "_trace_var"}, K trace_var_tr)]
end
*}

translations
  "[P \<turnstile> Q | R]\<^sub>R" => "CONST mk_RD P (\<lambda> _trace_var. Q) (\<lambda> _trace_var. R)"
  "[P \<turnstile> Q | R]\<^sub>R" <= "CONST mk_RD P (\<lambda> x. Q) (\<lambda> y. R)"
  "[P]\<^sub>t" => "CONST trace_pred (\<lambda> _trace_var. P)"
  "[P]\<^sub>t" <= "CONST trace_pred (\<lambda> t. P)"

  
lemma SRD_mk_RD [closure]: "[P \<turnstile> Q(trace) | R(trace)]\<^sub>R is SRD"
  by (simp add: mk_RD_def closure unrest)

lemma preR_mk_RD [rdes]: "pre\<^sub>R([P \<turnstile> Q(trace) | R(trace) ]\<^sub>R) = R1(\<lceil>P\<rceil>\<^sub>S\<^sub><)"
  by (simp add: mk_RD_def rea_pre_RHS_design usubst unrest R2c_not R2c_lift_state_pre)

lemma trace_pred_RR_closed [closure]: 
  "[P trace]\<^sub>t is RR"
  by (rel_auto)
    
lemma unrest_trace_pred_st' [unrest]:
  "$st\<acute> \<sharp> [P trace]\<^sub>t"
  by (rel_auto)
    
lemma R2c_msubst_tt: "R2c (msubst (\<lambda>x. \<lceil>Q x\<rceil>\<^sub>S) &tt) = (msubst (\<lambda>x. \<lceil>Q x\<rceil>\<^sub>S) &tt)"
  by (rel_auto)

lemma periR_mk_RD [rdes]: "peri\<^sub>R([P \<turnstile> Q(trace) | R(trace) ]\<^sub>R) = (\<lceil>P\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1((\<lceil>Q(trace)\<rceil>\<^sub>S\<^sub><)\<lbrakk>trace\<rightarrow>&tt\<rbrakk>))"
  by (simp add: mk_RD_def rea_peri_RHS_design usubst unrest R2c_not R2c_lift_state_pre
      R2c_disj R2c_msubst_tt R1_disj R2c_rea_impl R1_rea_impl)

lemma postR_mk_RD [rdes]: "post\<^sub>R([P \<turnstile> Q(trace) | R(trace) ]\<^sub>R) = (\<lceil>P\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1((\<lceil>R(trace)\<rceil>\<^sub>S)\<lbrakk>trace\<rightarrow>&tt\<rbrakk>))"
  by (simp add: mk_RD_def rea_post_RHS_design usubst unrest R2c_not R2c_lift_state_pre
      impl_alt_def R2c_disj R2c_msubst_tt R2c_rea_impl R1_rea_impl)

text {* Refinement introduction law for contracts *}

lemma RD_contract_refine:
  assumes
    "Q is SRD" "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R Q`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>2 x\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk>`"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2(trace) | P\<^sub>3(trace)]\<^sub>R \<sqsubseteq> Q"
proof -
  have "[P\<^sub>1 \<turnstile> P\<^sub>2(trace) | P\<^sub>3(trace)]\<^sub>R \<sqsubseteq> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    using assms
    by (simp add: mk_RD_def, rule_tac srdes_tri_refine_intro, simp_all)
  thus ?thesis
    by (simp add: SRD_reactive_tri_design assms(1))
qed

end