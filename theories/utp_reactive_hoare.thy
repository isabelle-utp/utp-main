section {* Hoare Logic for Reactive Processes *}

theory utp_reactive_hoare
  imports utp_rea_designs
begin

definition hoare_rp :: "'\<alpha> upred \<Rightarrow> ('\<alpha>, real pos) rdes \<Rightarrow> '\<alpha> upred \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<^sub>r") where
[upred_defs]: "hoare_rp p Q r = ((\<lceil>p\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<lceil>r\<rceil>\<^sub>S\<^sub>>) \<sqsubseteq> Q)"
  
lemma assigns_hoare_rp [hoare_safe]: "`p \<Rightarrow> \<sigma> \<dagger> q` \<Longrightarrow> \<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>r\<lbrace>q\<rbrace>\<^sub>r"
  by rel_auto

lemma skip_hoare_rp [hoare_safe]: "\<lbrace>p\<rbrace>II\<^sub>r\<lbrace>p\<rbrace>\<^sub>r"
  by rel_auto
    
lemma seq_hoare_rp: "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>s\<rbrace>\<^sub>r ; \<lbrace>s\<rbrace>Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>r \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>r"
  by (rel_auto)

lemma seq_est_hoare_rp [hoare_safe]: 
  "\<lbrakk> \<lbrace>true\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>r ; \<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>r \<rbrakk> \<Longrightarrow> \<lbrace>true\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>r"
  by (rel_auto)

lemma seq_inv_hoare_rp [hoare_safe]: 
  "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>r ; \<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>r \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>r"
  by (rel_auto)

lemma repeat_hoare_rp [hoare_safe]: 
  "\<lbrace>p\<rbrace>Q\<lbrace>p\<rbrace>\<^sub>r \<Longrightarrow> \<lbrace>p\<rbrace>Q \<^bold>^ n\<lbrace>p\<rbrace>\<^sub>r"
  by (induct n, rel_auto+)
    
lemma UINF_ind_hoare_rp [hoare_safe]: 
  "\<lbrakk> \<And> i. \<lbrace>p\<rbrace>Q(i)\<lbrace>r\<rbrace>\<^sub>r \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>\<Sqinter> i \<bullet> Q(i)\<lbrace>r\<rbrace>\<^sub>r"
  by (rel_auto)
    
lemma iter_hoare_rp [hoare_safe]: 
  "\<lbrace>p\<rbrace>Q\<lbrace>p\<rbrace>\<^sub>r \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sup>\<star>\<lbrace>p\<rbrace>\<^sub>r"
  by (simp add: ustar_def hoare_safe)    

lemma conj_hoare_rp [hoare_safe]:
  "\<lbrakk> \<lbrace>p\<^sub>1\<rbrace>Q\<^sub>1\<lbrace>r\<^sub>1\<rbrace>\<^sub>r; \<lbrace>p\<^sub>2\<rbrace>Q\<^sub>2\<lbrace>r\<^sub>2\<rbrace>\<^sub>r \<rbrakk> \<Longrightarrow> \<lbrace>p\<^sub>1 \<and> p\<^sub>2\<rbrace>Q\<^sub>1 \<and> Q\<^sub>2\<lbrace>r\<^sub>1 \<and> r\<^sub>2\<rbrace>\<^sub>r"
  by (rel_auto)
    
end