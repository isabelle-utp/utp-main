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

(* Changed *)

text {* Some of the following lemmas help backward reasoning with bindings *}

lemma conj_implies: "\<lbrakk> \<lbrakk>P \<and> Q\<rbrakk>\<^sub>e b \<rbrakk> \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e b \<and> \<lbrakk>Q\<rbrakk>\<^sub>e b"
  by pred_tac                                                            

lemma conj_implies2: "\<lbrakk> \<lbrakk>P\<rbrakk>\<^sub>e b \<and> \<lbrakk>Q\<rbrakk>\<^sub>e b \<rbrakk> \<Longrightarrow> \<lbrakk>P \<and> Q\<rbrakk>\<^sub>e b"
  by pred_tac

lemma disj_eq: "\<lbrakk> \<lbrakk>P\<rbrakk>\<^sub>e b \<or> \<lbrakk>Q\<rbrakk>\<^sub>e b \<rbrakk> \<Longrightarrow> \<lbrakk>P \<or> Q\<rbrakk>\<^sub>e b"
  by pred_tac

lemma disj_eq2: "\<lbrakk> \<lbrakk>P \<or> Q\<rbrakk>\<^sub>e b \<rbrakk> \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e b \<or> \<lbrakk>Q\<rbrakk>\<^sub>e b"
  by pred_tac

lemma conj_eq_subst: "(\<lbrakk>P \<and> Q\<rbrakk>\<^sub>e b \<and> \<lbrakk>P\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b) = (\<lbrakk>R \<and> Q\<rbrakk>\<^sub>e b \<and> \<lbrakk>P\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b)"
  by pred_tac

lemma conj_imp_subst: "(\<lbrakk>P \<and> Q\<rbrakk>\<^sub>e b \<and> (\<lbrakk>Q\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>P\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b))) = (\<lbrakk>R \<and> Q\<rbrakk>\<^sub>e b \<and> (\<lbrakk>Q\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>P\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b)))"
  by pred_tac

lemma disj_imp_subst: "(\<lbrakk>Q \<and> (P \<or> S)\<rbrakk>\<^sub>e b \<and> (\<lbrakk>Q\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>P\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b))) = (\<lbrakk>Q \<and> (R \<or> S)\<rbrakk>\<^sub>e b \<and> (\<lbrakk>Q\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>P\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b)))"
  by pred_tac

text {* Simplifications on value equality *}

lemma uexpr_eq: "(\<lbrakk>e\<^sub>0\<rbrakk>\<^sub>e b = \<lbrakk>e\<^sub>1\<rbrakk>\<^sub>e b) = \<lbrakk>e\<^sub>0 =\<^sub>u e\<^sub>1\<rbrakk>\<^sub>e b"
  by pred_tac

lemma uexpr_trans: "(\<lbrakk>P \<and> e\<^sub>0 =\<^sub>u e\<^sub>1\<rbrakk>\<^sub>e b \<and> (\<lbrakk>P\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>e\<^sub>1 =\<^sub>u e\<^sub>2\<rbrakk>\<^sub>e b)) = (\<lbrakk>P \<and> e\<^sub>0 =\<^sub>u e\<^sub>2\<rbrakk>\<^sub>e b \<and> (\<lbrakk>P\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>e\<^sub>1 =\<^sub>u e\<^sub>2\<rbrakk>\<^sub>e b))"
  by (pred_tac)

lemma uexpr_trans2: "(\<lbrakk>P \<and> Q \<and> e\<^sub>0 =\<^sub>u e\<^sub>1\<rbrakk>\<^sub>e b \<and> (\<lbrakk>Q\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>e\<^sub>1 =\<^sub>u e\<^sub>2\<rbrakk>\<^sub>e b)) = (\<lbrakk>P \<and> Q \<and> e\<^sub>0 =\<^sub>u e\<^sub>2\<rbrakk>\<^sub>e b \<and> (\<lbrakk>P\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>e\<^sub>1 =\<^sub>u e\<^sub>2\<rbrakk>\<^sub>e b))"
  by (pred_tac)

lemma uequality: "\<lbrakk> (\<lbrakk>R\<rbrakk>\<^sub>e b = \<lbrakk>Q\<rbrakk>\<^sub>e b) \<rbrakk> \<Longrightarrow> \<lbrakk>P \<and> R\<rbrakk>\<^sub>e b = \<lbrakk>P \<and> Q\<rbrakk>\<^sub>e b"
  by pred_tac

lemma ueqe1:"\<lbrakk> \<lbrakk>P\<rbrakk>\<^sub>e b \<Longrightarrow> (\<lbrakk>R\<rbrakk>\<^sub>e b = \<lbrakk>Q\<rbrakk>\<^sub>e b) \<rbrakk> \<Longrightarrow> (\<lbrakk>P \<and> R\<rbrakk>\<^sub>e b \<Longrightarrow> \<lbrakk>P \<and> Q\<rbrakk>\<^sub>e b)"
  by pred_tac

lemma ueqe2: "(\<lbrakk>P\<rbrakk>\<^sub>e b \<Longrightarrow> (\<lbrakk>Q\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b) \<and> \<lbrakk>Q \<and> P\<rbrakk>\<^sub>e b = \<lbrakk>R \<and> P\<rbrakk>\<^sub>e b) 
       \<Longrightarrow>
       (\<lbrakk>P\<rbrakk>\<^sub>e b \<Longrightarrow> (\<lbrakk>Q\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b))"
  by pred_tac

lemma ueqe3: "\<lbrakk> \<lbrakk>P\<rbrakk>\<^sub>e b \<Longrightarrow> (\<lbrakk>Q\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b) \<rbrakk> \<Longrightarrow> (\<lbrakk>R \<and> P\<rbrakk>\<^sub>e b = \<lbrakk>Q \<and> P\<rbrakk>\<^sub>e b)"
  by pred_tac

text {* The following allows simplifying the equality if P \<Rightarrow> Q = R *}

lemma ueqe3_imp: "(\<And> b. \<lbrakk>P\<rbrakk>\<^sub>e b \<Longrightarrow> (\<lbrakk>Q\<rbrakk>\<^sub>e b = \<lbrakk>R\<rbrakk>\<^sub>e b)) \<Longrightarrow> ((R \<and> P) = (Q \<and> P))"
  by pred_tac

lemma ueqe3_imp2: "\<lbrakk> (\<And> b. \<lbrakk>P0 \<and> P1\<rbrakk>\<^sub>e b \<Longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e b \<Longrightarrow> \<lbrakk>R\<rbrakk>\<^sub>e b = \<lbrakk>S\<rbrakk>\<^sub>e b) \<rbrakk> \<Longrightarrow> ((P0 \<and> P1 \<and> (Q \<Rightarrow> R)) = (P0 \<and> P1 \<and> (Q \<Rightarrow> S)))"
  by pred_tac

text {* The following can introduce the binding notation into predicates *}

lemma conj_bind_dist: "\<lbrakk>P \<and> Q\<rbrakk>\<^sub>e b = (\<lbrakk>P\<rbrakk>\<^sub>e b \<and> \<lbrakk>Q\<rbrakk>\<^sub>e b)"
  by pred_tac

lemma disj_bind_dist: "\<lbrakk>P \<or> Q\<rbrakk>\<^sub>e b = (\<lbrakk>P\<rbrakk>\<^sub>e b \<or> \<lbrakk>Q\<rbrakk>\<^sub>e b)"
  by pred_tac

lemma imp_bind_dist: "\<lbrakk>P \<Rightarrow> Q\<rbrakk>\<^sub>e b = (\<lbrakk>P\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e b)"
  by pred_tac

end