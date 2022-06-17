section \<open> Separation Logic \<close>

theory utp_mem_seplog
  imports utp_mem_aseplog utp_mem_prog
begin

definition heaplet :: "(addr, 's) uexpr \<Rightarrow> ('a::{countable,infinite}, 's) uexpr \<Rightarrow> 's mpred" (infix "\<^bold>\<mapsto>" 70) where
[upred_defs]: "v \<^bold>\<mapsto> e = (dom\<^sub>u(&hp) =\<^sub>u {v \<oplus>\<^sub>p str}\<^sub>u \<and> &hp(v \<oplus>\<^sub>p str)\<^sub>a =\<^sub>u uop to_nat_bij (e \<oplus>\<^sub>p str))"

abbreviation heaplet_min :: "(addr, 's) uexpr \<Rightarrow> ('a::{countable,infinite}, 's) uexpr \<Rightarrow> 's mpred" (infix "\<^bold>\<hookrightarrow>" 70) where
"v \<^bold>\<hookrightarrow> e \<equiv> v \<^bold>\<mapsto> e \<^bold>* true"

abbreviation heaplet_ex :: "(addr, 's) uexpr \<Rightarrow> 's mpred" ("_ \<^bold>\<mapsto> -" [69] 70) where
"e \<^bold>\<mapsto> - \<equiv> (\<^bold>\<exists> v::nat \<bullet> e \<^bold>\<mapsto> \<guillemotleft>v\<guillemotright>)"

lemma local_wrt_heap_lookup: 
  "\<lbrakk> vwb_lens x; x \<sharp> e; str:x \<sharp> p \<rbrakk> \<Longrightarrow> local_wrt p (x := *e)"
  apply (rel_simp)
  apply (rename_tac q st hp0 hp1)
  apply (rule_tac x="hp0" in exI)
  apply (auto)
  done

subsection \<open> Separation Logic Laws \<close>

lemma allocation_noninterfering_local:
  "{emp}v := alloc(e){&v \<^bold>\<mapsto> e}\<^sub>D"
  by (rel_auto)

lemma allocation_noninterfering_global:
  "\<lbrakk> vwb_lens x; str:x \<sharp> p \<rbrakk> \<Longrightarrow> {p}x := alloc(e){p \<^bold>* &x \<^bold>\<mapsto> e}\<^sub>D"
  apply (rel_simp)
  apply (rename_tac ok hp st ok' l)
  apply (rule_tac x="hp" in exI)
  apply (rule_tac x="bot(l \<mapsto> to_nat_bij (\<lbrakk>e\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> st l)))\<^sub>f" in exI)
  apply (simp add: ffun_indep_compat)
  done

lemma mutation_local: "{e \<^bold>\<mapsto> -} *e := v {e \<^bold>\<mapsto> v}\<^sub>D"
  by (rel_auto)

lemma mutation_global: "{p \<^bold>* e \<^bold>\<mapsto> -} *e := v {p \<^bold>* e \<^bold>\<mapsto> v}\<^sub>D"
  apply (rel_simp)
  apply (rename_tac st ok' a b x)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="b(\<lbrakk>e\<rbrakk>\<^sub>e st \<mapsto> to_nat_bij (\<lbrakk>v\<rbrakk>\<^sub>e st))\<^sub>f" in exI)
  apply (auto simp add: compatible_ffun_def compatible_pfun_def)
  oops

lemma deallocation_local:
  "{e \<^bold>\<mapsto> -} dealloc(e) {emp}\<^sub>D"
  by (rel_auto)

lemma deallocation_global:
  "{r \<^bold>* e \<^bold>\<mapsto> -} dealloc(e) {r}\<^sub>D"
  apply (rel_simp)
  apply (rename_tac ok st ok' a b x)
  apply (subgoal_tac "fdom(a) \<lhd>\<^sub>f b = fdom(a) \<lhd>\<^sub>f (fdom(b) \<lhd>\<^sub>f b)")
   apply (simp add: compatible_ffun_def)
  oops

lemma lookup_global:
  "\<lbrakk> vwb_lens x; x \<sharp> e; x \<sharp> v; str:x \<sharp> r \<rbrakk> \<Longrightarrow> 
    {r \<^bold>* e \<^bold>\<mapsto> v} x := *e {r \<^bold>* (&str:x =\<^sub>u (v \<oplus>\<^sub>p str) \<and> e \<^bold>\<mapsto> v)}\<^sub>D"
  by (rel_auto)
  
end