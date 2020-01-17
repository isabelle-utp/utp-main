section \<open> Morgan's Relational Refinement Calculus \<close>

theory morgan_rcalc
  imports "UTP.utp"
begin

subsection \<open> Specification Statement \<close>

definition spec :: "('a \<Longrightarrow> 's) \<Rightarrow> 's upred \<Rightarrow> 's upred \<Rightarrow> 's hrel" ("_:[_,_]" [900, 0, 0] 900) where
[upred_defs]: "spec w p q = (p\<^sup>< \<Rightarrow> q\<^sup>> \<and> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v \<oplus> $\<^bold>v\<acute> on &w)"

utp_lift_notation spec (1 2)

subsection \<open> Refinement Laws \<close>

lemma strengthen_post:
  assumes "`post' \<Rightarrow> post`"
  shows "w:[pre, post] \<sqsubseteq> w:[pre, post']"
  using assms by (rel_auto)

lemma weaken_pre:
  assumes "`pre \<Rightarrow> pre'`"
  shows "w:[pre, post] \<sqsubseteq> w:[pre', post]"
  using assms by (rel_auto)

lemma refine_skip:
  assumes "vwb_lens w" "`pre \<Rightarrow> post`"
  shows "w:[pre, post] \<sqsubseteq> II"
  using assms by (rel_auto)

lemma refine_assign:
  assumes "vwb_lens w" "vwb_lens x" "x \<subseteq>\<^sub>L w" "`pre \<Rightarrow> post\<lbrakk>e/x\<rbrakk>`"
  shows "w:[pre, post] \<sqsubseteq> x := e"
  using assms by (rel_auto)

lemma assign_is_spec:
  assumes "vwb_lens w" "w \<sharp> e" 
  shows "(w := e) = w:[true, &w = e]"
  using assms by (rel_auto, metis)

lemma refine_seq:
  "vwb_lens a \<Longrightarrow> a:[pre, post] \<sqsubseteq> a:[pre, mid] ;; a:[mid, post]"
  by (rel_simp, metis vwb_lens.put_eq)

lemma refine_assign_follow:
  assumes "vwb_lens w" "vwb_lens x" "x \<subseteq>\<^sub>L w"
  shows "w:[pre, post] \<sqsubseteq> w:[pre, post\<lbrakk>e/x\<rbrakk>] ;; x := e" 
  using assms
  by (rel_auto, metis (no_types, lifting) mwb_lens.put_put vwb_lens_mwb)

lemma refine_frame:
  "\<lbrakk> vwb_lens x; x \<bowtie> w \<rbrakk> \<Longrightarrow> {x,w}\<^sub>v:[pre, post] \<sqsubseteq> w:[pre, post]"
  by (rel_simp)

lemma refine_cond:
  "x:[pre, post] \<sqsubseteq> x:[b \<and> pre, post] \<triangleleft> b \<triangleright>\<^sub>r x:[\<not>b \<and> pre, post]"
  by (rel_auto)

subsection \<open> Examples \<close>

alphabet ss = x :: real y :: real

abbreviation (input) "s1 \<equiv> y:[0 \<le> x \<and> x \<le> 9, y\<^sup>2 = x]"
abbreviation (input) "s2 \<equiv> y:[0 \<le> x \<and> x \<le> 9, y\<^sup>2 = x \<and> 0 \<le> y]"

lemma "s1 \<sqsubseteq> s2"
  apply (rule strengthen_post)
  apply (rel_auto)
  done

abbreviation (input) "s3 \<equiv> y:[0 \<le> x, y\<^sup>2 = x \<and> 0 \<le> y]"

lemma "s2 \<sqsubseteq> s3"
  apply (rule weaken_pre)
  apply (rel_auto)
  done

lemma "s3 \<sqsubseteq> y := sqrt(x)"
  apply (rule refine_assign)
     apply (simp_all)
  apply (rel_auto)
  done

alphabet sse = ss + t::real

end