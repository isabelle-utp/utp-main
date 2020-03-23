section \<open> Weakest Liberal Precondition Calculus \<close>

theory utp_wlp
imports utp_hoare
begin

text \<open> The calculus we here define is termed ``weakest precondition'' in the UTP book, however
  it is in reality the liberal version that does not account for termination. \<close>

named_theorems wp

method wp_tac = (simp add: wp usubst unrest)

consts
  uwlp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "wlp" 60)

definition wlp_upred :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> cond \<Rightarrow> '\<alpha> cond" where
"wlp_upred Q r = \<lfloor>\<not> (Q ;; (\<not> \<lceil>r\<rceil>\<^sub><)) :: ('\<alpha>, '\<beta>) urel\<rfloor>\<^sub><"

utp_const uwlp (0)

adhoc_overloading
  uwlp wlp_upred

declare wlp_upred_def [urel_defs]

lemma wlp_true [wp]: "p wlp true = true"
  by (rel_simp)  

lemma wlp_conj [wp]: "(P wlp (b \<and> c)) = ((P wlp b) \<and> (P wlp c))"
  by (rel_auto)

theorem wlp_assigns_r [wp]:
  "\<langle>\<sigma>\<rangle>\<^sub>a wlp r = \<sigma> \<dagger> r"
  by rel_auto

lemma wlp_nd_assign [wp]: "(x := *) wlp b = (\<^bold>\<forall> v \<bullet> b\<lbrakk>\<guillemotleft>v\<guillemotright>/&x\<rbrakk>)"
  by (simp add: nd_assign_def wp, rel_auto)

lemma wlp_rel_aext_unrest [wp]: "\<lbrakk> vwb_lens a; a \<sharp> b \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ wlp b = ((P wlp false) \<oplus>\<^sub>p a \<or> b)"
  by (rel_simp, metis mwb_lens_def vwb_lens_def weak_lens.put_get)

lemma wlp_rel_aext_usedby [wp]: "\<lbrakk> vwb_lens a; a \<natural> b \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ wlp b = (P wlp (b \<restriction>\<^sub>e a)) \<oplus>\<^sub>p a"
  by (rel_auto, metis mwb_lens_def vwb_lens_mwb weak_lens.put_get)

theorem wlp_skip_r [wp]:
  "II wlp r = r"
  by rel_auto

theorem wlp_abort [wp]:
  "r \<noteq> true \<Longrightarrow> true wlp r = false"
  by rel_auto

theorem wlp_seq_r [wp]: "(P ;; Q) wlp r = P wlp (Q wlp r)"
  by rel_auto

theorem wlp_choice [wp]: "(P \<sqinter> Q) wlp R = (P wlp R \<and> Q wlp R)"
  by (rel_auto)

theorem wlp_choice' [wp]: "(P \<or> Q) wlp R = (P wlp R \<and> Q wlp R)"
  by (rel_auto)

theorem wlp_cond [wp]: "(P \<triangleleft> b \<triangleright>\<^sub>r Q) wlp r = ((b \<Rightarrow> P wlp r) \<and> ((\<not> b) \<Rightarrow> Q wlp r))"
  by rel_auto

lemma wlp_UINF_ind [wp]: "(\<Sqinter> i \<bullet> P(i)) wlp b = (\<^bold>\<forall> i \<bullet> P(i) wlp b)"
  by (rel_auto)

lemma wlp_test [wp]: "?[b] wlp c = (b \<Rightarrow> c)"
  by (rel_auto)
 
lemma wlp_gcmd [wp]: "(b \<longrightarrow>\<^sub>r P) wlp c = (b \<Rightarrow> P wlp c)"
  by (simp add: rgcmd_def wp)

term "U(\<forall> i\<in>{0..n}. i < n)"

declare [[show_types]]

term "U(\<forall> i\<in>{0..n}. P wlp @(Q i))"

term "\<guillemotleft>All\<guillemotright> |> (\<lambda> i \<bullet> @(P wlp Q i))"

lemma wlp_USUP_pre [wp]: "P wlp (\<And> i\<in>{0..n} \<bullet> Q(i)) = U(\<forall> i\<in>\<guillemotleft>{0..n}\<guillemotright>. @(P wlp Q i))"
  by (rel_auto; blast)

theorem wlp_hoare_link:
  "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u \<longleftrightarrow> `p \<Rightarrow> Q wlp r`"
  by rel_auto

text \<open> We can use the above theorem as a means to discharge Hoare triples with the following tactic \<close>

method hoare_wlp_auto uses defs = (simp add: wlp_hoare_link wp unrest usubst defs; rel_auto)

text \<open> If two programs have the same weakest precondition for any postcondition then the programs
  are the same. \<close>

theorem wlp_eq_intro: "\<lbrakk> \<And> r. P wlp r = Q wlp r \<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto robust, fastforce+)

end