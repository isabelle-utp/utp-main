section {* UTP Deduction Tactic *}

theory utp_deduct
imports utp_pred
begin

lemma uopI: "f (\<lbrakk>x\<rbrakk>\<^sub>eb) \<Longrightarrow> \<lbrakk>uop f x\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma bopI: "f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) \<Longrightarrow> \<lbrakk>bop f x y\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma tropI: "f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) \<Longrightarrow> \<lbrakk>trop f x y z\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma uconjI: "\<lbrakk> \<lbrakk>p\<rbrakk>\<^sub>eb; \<lbrakk>q\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>p \<and> q\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma uiffI: "\<lbrakk> \<And> b. \<lbrakk>p\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>eb; \<And> b. \<lbrakk>q\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>p\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> p = q"
  by (pred_tac)

lemma uimpI: "\<lbrakk> \<lbrakk>p\<rbrakk>\<^sub>eb \<Longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>p \<Rightarrow> q\<rbrakk>\<^sub>eb"
  by (pred_tac)

lemma ushAllI: "\<lbrakk> \<And> x. \<lbrakk>p(x)\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>\<^bold>\<forall> x \<bullet> p(x)\<rbrakk>\<^sub>eb" 
  by pred_tac

lemma ushExI: "\<lbrakk> \<lbrakk>p(x)\<rbrakk>\<^sub>eb \<rbrakk> \<Longrightarrow> \<lbrakk>\<^bold>\<exists> x \<bullet> p(x)\<rbrakk>\<^sub>eb" 
  by pred_tac

end