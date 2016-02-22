section {* UTP Deduction Tactic *}

theory utp_deduct
imports utp_pred
begin

named_theorems uintro
named_theorems uelim
named_theorems udest

lemma utrueI [uintro]: "\<lbrakk>true\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma uopI [uintro]: "f (\<lbrakk>x\<rbrakk>\<^sub>eb) \<Longrightarrow> \<lbrakk>uop f x\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma bopI [uintro]: "f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) \<Longrightarrow> \<lbrakk>bop f x y\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma tropI [uintro]: "f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) \<Longrightarrow> \<lbrakk>trop f x y z\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma uconjI [uintro]: "\<lbrakk> \<lbrakk>p\<rbrakk>\<^sub>eb; \<lbrakk>q\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>p \<and> q\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma uconjE [uelim]: "\<lbrakk> \<lbrakk>p \<and> q\<rbrakk>\<^sub>eb; \<lbrakk> \<lbrakk>p\<rbrakk>\<^sub>eb ; \<lbrakk>q\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (pred_tac)

lemma uimpI [uintro]: "\<lbrakk> \<lbrakk>p\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>p \<Rightarrow> q\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma uimpE [elim]: "\<lbrakk> \<lbrakk>p \<Rightarrow> q\<rbrakk>\<^sub>eb; (\<lbrakk>p\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>eb) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (pred_tac)

lemma ushAllI [uintro]: "\<lbrakk> \<And> x. \<lbrakk>p(x)\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>\<^bold>\<forall> x \<bullet> p(x)\<rbrakk>\<^sub>eb" 
  by pred_tac

lemma ushExI [uintro]: "\<lbrakk> \<lbrakk>p(x)\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>\<^bold>\<exists> x \<bullet> p(x)\<rbrakk>\<^sub>eb" 
  by pred_tac

lemma udeduct_tautI [uintro]: "\<lbrakk> \<And> b. \<lbrakk>p\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> `p`"
  using taut.rep_eq by blast

lemma udeduct_refineI [uintro]: "\<lbrakk> \<And> b. \<lbrakk>q\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>p\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> p \<sqsubseteq> q"
  by pred_tac

lemma udeduct_eqI [uintro]: "\<lbrakk> \<And> b. \<lbrakk>p\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>eb; \<And> b. \<lbrakk>q\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>p\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> p = q"
  by (pred_tac)

end