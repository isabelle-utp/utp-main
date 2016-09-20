subsection {* Relational Hoare calculus *}

theory utp_hoare
imports utp_rel
begin

named_theorems hoare

definition hoare_r :: "'\<alpha> condition \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> condition \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>u") where
"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u = ((\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>r\<rceil>\<^sub>>) \<sqsubseteq> Q)"

declare hoare_r_def [upred_defs]

lemma hoare_r_conj [hoare]: "\<lbrakk> \<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u; \<lbrace>p\<rbrace>Q\<lbrace>s\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<lbrace>r \<and> s\<rbrace>\<^sub>u"
  by rel_tac

lemma hoare_r_conseq [hoare]: "\<lbrakk> `p\<^sub>1 \<Rightarrow> p\<^sub>2`; \<lbrace>p\<^sub>2\<rbrace>S\<lbrace>q\<^sub>2\<rbrace>\<^sub>u; `q\<^sub>2 \<Rightarrow> q\<^sub>1` \<rbrakk> \<Longrightarrow> \<lbrace>p\<^sub>1\<rbrace>S\<lbrace>q\<^sub>1\<rbrace>\<^sub>u"
  by rel_tac

lemma assigns_hoare_r [hoare]: "`p \<Rightarrow> \<sigma> \<dagger> q` \<Longrightarrow> \<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>q\<rbrace>\<^sub>u"
  by rel_tac

lemma skip_hoare_r [hoare]: "\<lbrace>p\<rbrace>II\<lbrace>p\<rbrace>\<^sub>u"
  by rel_tac  

lemma seq_hoare_r [hoare]: "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>s\<rbrace>\<^sub>u ; \<lbrace>s\<rbrace>Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>u"
  by rel_tac

lemma cond_hoare_r [hoare]: "\<lbrakk> \<lbrace>b \<and> p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u ; \<lbrace>\<not>b \<and> p\<rbrace>T\<lbrace>q\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>S \<triangleleft> b \<triangleright>\<^sub>r T\<lbrace>q\<rbrace>\<^sub>u"
  by rel_tac

lemma while_hoare_r [hoare]: 
  assumes "\<lbrace>p \<and> b\<rbrace>S\<lbrace>p\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>while b do S od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u"
proof -
  from assms have "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>p\<rceil>\<^sub>>) \<sqsubseteq> (II \<sqinter> ((\<lceil>b\<rceil>\<^sub>< \<and> S) ;; (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>p\<rceil>\<^sub>>)))"
    by (simp add: hoare_r_def) (rel_tac)  
  hence p: "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>p\<rceil>\<^sub>>) \<sqsubseteq> (\<lceil>b\<rceil>\<^sub>< \<and> S)\<^sup>\<star>\<^sub>u"
    by (rule upred_quantale.star_inductl_one[rule_format])
  have "(\<not>\<lceil>b\<rceil>\<^sub>> \<and> \<lceil>p\<rceil>\<^sub>>) \<sqsubseteq> ((\<lceil>p\<rceil>\<^sub>< \<and> (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>p\<rceil>\<^sub>>)) \<and> (\<not>\<lceil>b\<rceil>\<^sub>>))"
    by (rel_tac)
  with p have "(\<not>\<lceil>b\<rceil>\<^sub>> \<and> \<lceil>p\<rceil>\<^sub>>) \<sqsubseteq> ((\<lceil>p\<rceil>\<^sub>< \<and> (\<lceil>b\<rceil>\<^sub>< \<and> S)\<^sup>\<star>\<^sub>u) \<and> (\<not>\<lceil>b\<rceil>\<^sub>>))"
    by (meson order_refl order_trans utp_pred.inf_mono)
  thus ?thesis
    unfolding hoare_r_def while_def
    by (auto intro: spec_refine simp add: alpha utp_pred.conj_assoc)
qed

lemma while_invr_hoare_r [hoare]:
  assumes "\<lbrace>p \<and> b\<rbrace>S\<lbrace>p\<rbrace>\<^sub>u" "`pre \<Rightarrow> p`" "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p do S od\<lbrace>post\<rbrace>\<^sub>u"
  by (metis assms hoare_r_conseq while_hoare_r while_inv_def)

end