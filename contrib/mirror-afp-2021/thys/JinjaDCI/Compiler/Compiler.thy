(*  Title:      JinjaDCI/Compiler/Compiler.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   TUM 2003, UIUC 2019-20

    Based on the Jinja theory Compiler/Compiler.thy by Tobias Nipkow
*)

section \<open> Combining Stages 1 and 2 \<close>

theory Compiler
imports Correctness1 Correctness2
begin

definition J2JVM :: "J_prog \<Rightarrow> jvm_prog"
where 
  "J2JVM  \<equiv>  compP\<^sub>2 \<circ> compP\<^sub>1"

theorem comp_correct_NonStatic:
assumes wf: "wf_J_prog P"
and "method": "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in C"
and eval: "P \<turnstile> \<langle>body,(h,[this#pns [\<mapsto>] vs],sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>"
and sizes: "size vs = size pns + 1"    "size rest = max_vars body"
shows "J2JVM P \<turnstile> (None,h,[([],vs@rest,C,M,0,No_ics)],sh) -jvm\<rightarrow> (exception e',h',[],sh')"
(*<*)
proof -
  let ?P\<^sub>1 = "compP\<^sub>1 P"
  have nclinit: "M \<noteq> clinit" using wf_sees_clinit1[OF wf] visible_method_exists[OF "method"]
    sees_method_idemp[OF "method"] by fastforce
  have wf\<^sub>1: "wf_J\<^sub>1_prog ?P\<^sub>1" by(rule compP\<^sub>1_pres_wf[OF wf])
  have fv: "fv body \<subseteq> set (this#pns)"
    using wf_prog_wwf_prog[OF wf] "method" by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have init: "[this#pns [\<mapsto>] vs] \<subseteq>\<^sub>m [this#pns [\<mapsto>] vs@rest]"
    using sizes by simp
  have "?P\<^sub>1 \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (compE\<^sub>1 (this#pns) body) in C"
    using sees_method_compP[OF "method", of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  moreover obtain ls' where
    "?P\<^sub>1 \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 (this#pns) body, (h, vs@rest, sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e', (h',ls', sh')\<rangle>"
    using eval\<^sub>1_eval[OF wf_prog_wwf_prog[OF wf] eval fv init] sizes by auto
  ultimately show ?thesis using comp\<^sub>2_correct[OF wf\<^sub>1] eval_final[OF eval] nclinit
    by(fastforce simp add:J2JVM_def final_def)
qed
(*>*)

theorem comp_correct_Static:
assumes wf: "wf_J_prog P"
and "method": "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in C"
and eval: "P \<turnstile> \<langle>body,(h,[pns [\<mapsto>] vs],sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>"
and sizes: "size vs = size pns"    "size rest = max_vars body"
and nclinit: "M \<noteq> clinit"
shows "J2JVM P \<turnstile> (None,h,[([],vs@rest,C,M,0,No_ics)],sh) -jvm\<rightarrow> (exception e',h',[],sh')"
(*<*)
proof -
  let ?P\<^sub>1 = "compP\<^sub>1 P"
  have wf\<^sub>1: "wf_J\<^sub>1_prog ?P\<^sub>1" by(rule compP\<^sub>1_pres_wf[OF wf])
  have fv: "fv body \<subseteq> set pns"
    using wf_prog_wwf_prog[OF wf] "method" by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have init: "[pns [\<mapsto>] vs] \<subseteq>\<^sub>m [pns [\<mapsto>] vs@rest]"
    using sizes by simp
  have "?P\<^sub>1 \<turnstile> C sees M,Static: Ts\<rightarrow>T = (compE\<^sub>1 pns body) in C"
    using sees_method_compP[OF "method", of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  moreover obtain ls' where
    "?P\<^sub>1 \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 pns body, (h, vs@rest, sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e', (h',ls', sh')\<rangle>"
    using eval\<^sub>1_eval[OF wf_prog_wwf_prog[OF wf] eval fv init] sizes by auto
  ultimately show ?thesis using comp\<^sub>2_correct[OF wf\<^sub>1] eval_final[OF eval] nclinit
    by(fastforce simp add:J2JVM_def final_def)
qed
(*>*)

end
