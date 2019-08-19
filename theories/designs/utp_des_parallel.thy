section \<open> Designs parallel-by-merge \<close>

theory utp_des_parallel
  imports utp_des_prog
begin

subsection \<open> Definitions \<close>

text \<open> We introduce the parametric design merge, which handles merging of the $ok$ variables, and
  leaves the other variables to the parametrised "inner" merge predicate. As expected, a parallel
  composition of designs can diverge whenever one of its arguments can. \<close>

definition des_merge :: "(('\<alpha>, '\<beta>, '\<gamma>) mrg, '\<delta>) urel \<Rightarrow> (('\<alpha> des, '\<beta> des, '\<gamma> des) mrg, '\<delta> des) urel" ("\<^bold>D\<^bold>M'(_')") where
[upred_defs]: "\<^bold>D\<^bold>M(M) \<equiv> (($0:ok \<and> $1:ok \<Rightarrow> $ok\<acute> \<and> $\<^bold>v\<^sub>D:0\<acute> =\<^sub>u $0:\<^bold>v\<^sub>D \<and> $\<^bold>v\<^sub>D:1\<acute> =\<^sub>u $1:\<^bold>v\<^sub>D \<and> $\<^bold>v\<^sub>D:<\<acute> =\<^sub>u $<:\<^bold>v\<^sub>D) ;; (true \<turnstile>\<^sub>n M))"

text \<open> Parallel composition is then defined via the above merge predicate and the standard UTP
  parallel-by-merge operator. \<close>

abbreviation
  dpar_by_merge :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> (('\<alpha>, '\<beta>, '\<gamma>) mrg, '\<delta>) urel \<Rightarrow> ('\<alpha>, '\<gamma>) rel_des \<Rightarrow> ('\<alpha>, '\<delta>) rel_des" 
  ("_ \<parallel>\<^sup>D\<^bsub>_\<^esub> _" [85,0,86] 85)
  where "P \<parallel>\<^sup>D\<^bsub>M\<^esub> Q \<equiv> P \<parallel>\<^bsub>\<^bold>D\<^bold>M(M)\<^esub> Q"

subsection \<open> Theorems \<close>

text \<open> The design merge predicate is symmetric up to the inner merge predicate. \<close>

lemma swap_des_merge: "swap\<^sub>m ;; \<^bold>D\<^bold>M(M) = \<^bold>D\<^bold>M(swap\<^sub>m ;; M)"
  by (rel_auto)

text \<open> The following laws explain the meaning of a merge of two normal (@{term H3}) designs. 
  The postcondition is straightforward: we simply distribute the inner merge. However, the 
  precondition is more complex. We'd be forgiven for thinking it would simply be $p \wedge q$, but
  this does not account for the possibility of miraculous behaviour in either argument. When this
  occurs, divergence is effectively overshadowed by miraculous behaviour, and so the precondition
  needs to involve the relational preconditions of both the design commitments ($P$ and $Q$). \<close>

lemma ndes_merge_aux: 
  "(p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>M\<^esub> (q \<turnstile>\<^sub>n Q) =(\<not> Pre(\<not> p\<^sup>< \<and> (q\<^sup>< \<Rightarrow> Q)) \<and> \<not> Pre(\<not> q\<^sup>< \<and> (p\<^sup>< \<Rightarrow> P))) \<turnstile>\<^sub>n (P \<parallel>\<^bsub>M\<^esub> Q)"
proof -
  have p2: "(\<lceil>p \<turnstile>\<^sub>n P\<rceil>\<^sub>0 \<and> \<lceil>q \<turnstile>\<^sub>n Q\<rceil>\<^sub>1 \<and> $<\<acute> =\<^sub>u $\<^bold>v) ;; 
            ($0:ok \<and> $1:ok \<Rightarrow> $ok\<acute> \<and> $\<^bold>v\<^sub>D:0\<acute> =\<^sub>u $0:\<^bold>v\<^sub>D \<and> $\<^bold>v\<^sub>D:1\<acute> =\<^sub>u $1:\<^bold>v\<^sub>D \<and> $\<^bold>v\<^sub>D:<\<acute> =\<^sub>u $<:\<^bold>v\<^sub>D)
            = (\<not> Pre(\<not> p\<^sup>< \<and> (q\<^sup>< \<Rightarrow> Q)) \<and> \<not> Pre(\<not> q\<^sup>< \<and> (p\<^sup>< \<Rightarrow> P))) \<turnstile>\<^sub>n (\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> $<:\<^bold>v\<acute> =\<^sub>u $\<^bold>v)"
    by (rel_auto, metis+)
  show ?thesis    
    by (simp add: des_merge_def par_by_merge_alt_def seqr_assoc[THEN sym] ndesign_composition_wp wp p2)
qed

lemma ndes_merge: 
  "(p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>M\<^esub> (q \<turnstile>\<^sub>n Q) =((p \<or> q \<and> \<not>Pre(Q)) \<and> (q \<or> p \<and> \<not>Pre(P))) \<turnstile>\<^sub>n (P \<parallel>\<^bsub>M\<^esub> Q)"
  by (simp add: ndes_merge_aux, rel_auto)

lemma ndes_merge_wlp: 
  "(p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>M\<^esub> (q \<turnstile>\<^sub>n Q) =((p \<or> q \<and> Q wlp false) \<and> (q \<or> p \<and> P wlp false)) \<turnstile>\<^sub>n (P \<parallel>\<^bsub>M\<^esub> Q)"
  by (simp add: ndes_merge_aux, rel_auto)

text \<open> If the commitments are both total relations, then we do indeed get a precondition of simply
  $p \wedge q$. \<close>

lemma ndes_merge_total: 
  assumes "Pre(P) = true" "Pre(Q) = true"
  shows "(p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>M\<^esub> (q \<turnstile>\<^sub>n Q) =(p \<and> q) \<turnstile>\<^sub>n (P \<parallel>\<^bsub>M\<^esub> Q)"
  by (simp add: ndes_merge assms)

lemma ndes_merge_assigns: "(p\<^sub>1 \<turnstile>\<^sub>n \<langle>\<sigma>\<rangle>\<^sub>a) \<parallel>\<^sup>D\<^bsub>M\<^esub> (q\<^sub>1 \<turnstile>\<^sub>n \<langle>\<rho>\<rangle>\<^sub>a) = (p\<^sub>1 \<and> q\<^sub>1) \<turnstile>\<^sub>n (\<langle>\<sigma>\<rangle>\<^sub>a \<parallel>\<^bsub>M\<^esub> \<langle>\<rho>\<rangle>\<^sub>a)" (is "?lhs = ?rhs")
  by (rule ndes_merge_total, simp_all add: Pre_assigns)

lemma ndes_merge_H1_H3_closed [closure]: 
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "P \<parallel>\<^sup>D\<^bsub>M\<^esub> Q is \<^bold>N"
  by (metis assms ndes_merge ndesign_H1_H3 ndesign_form)

end