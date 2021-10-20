subsection \<open>UTP theory of Designs\<close>

theory utp_des_theory
  imports utp_des_healths
begin
  
subsection \<open>UTP theories\<close>

interpretation des_theory: utp_theory_continuous "\<^bold>H"
  rewrites "P \<in> carrier des_theory.thy_order \<longleftrightarrow> P is \<^bold>H"
  and "carrier des_theory.thy_order \<rightarrow> carrier des_theory.thy_order \<equiv> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
  and "le des_theory.thy_order = (\<sqsubseteq>)"
  and "eq des_theory.thy_order = (=)"  
  and des_top: "des_theory.utp_top = \<top>\<^sub>D"
  and des_bottom: "des_theory.utp_bottom = \<bottom>\<^sub>D"
proof -
  show "utp_theory_continuous \<^bold>H"
    by (unfold_locales, simp_all add: H1_H2_idempotent H1_H2_Continuous)
  then interpret utp_theory_continuous "\<^bold>H"
    by simp
  show "utp_top = \<top>\<^sub>D" "utp_bottom = \<bottom>\<^sub>D"
    by (simp_all add: H1_H2_false healthy_top H1_H2_true healthy_bottom)
qed (simp_all)

interpretation ndes_theory: utp_theory_continuous "\<^bold>N"
  rewrites "P \<in> carrier ndes_theory.thy_order \<longleftrightarrow> P is \<^bold>N"
  and "carrier ndes_theory.thy_order \<rightarrow> carrier ndes_theory.thy_order \<equiv> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  and "le ndes_theory.thy_order = (\<sqsubseteq>)"
  and "eq ndes_theory.thy_order = (=)"  
  and ndes_top: "ndes_theory.utp_top = \<top>\<^sub>D"
  and ndes_bottom: "ndes_theory.utp_bottom = \<bottom>\<^sub>D"
proof -
  show "utp_theory_continuous \<^bold>N"
    by (unfold_locales, simp_all add: H1_H3_idempotent H1_H3_Continuous)
  then interpret utp_theory_continuous "\<^bold>N"
    by simp
  show "utp_top = \<top>\<^sub>D" "utp_bottom = \<bottom>\<^sub>D"
    by (simp_all add: H1_H3_false healthy_top H1_H3_true healthy_bottom)
qed (simp_all)

interpretation des_left_unital: utp_theory_left_unital "\<^bold>H" "II\<^sub>D"
  by (unfold_locales, simp_all add: H1_H2_left_unit closure)

interpretation ndes_unital: utp_theory_unital "\<^bold>N" "II\<^sub>D"
  by (unfold_locales, simp_all add: H1_H3_left_unit H1_H3_right_unit closure)

interpretation ndes_kleene: utp_theory_kleene "\<^bold>N" II\<^sub>D
  by (unfold_locales, simp add: ndes_top H1_H3_top_left)

abbreviation ndes_star :: "_ \<Rightarrow> _"  ("_\<^sup>\<star>\<^sup>D" [999] 999) where
"P\<^sup>\<star>\<^sup>D \<equiv> ndes_unital.utp_star"

subsection \<open>Galois Connection\<close>

text \<open>Example Galois connection between designs and relations. Based on Jim's example in COMPASS
        deliverable D23.5.\<close>

definition [upred_defs]: "Des(R) = \<^bold>H(\<lceil>R\<rceil>\<^sub>D \<and> $ok\<acute>)"
definition [upred_defs]: "Rel(D) = \<lfloor>D\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>\<rfloor>\<^sub>D"

lemma Des_design: "Des(R) = true \<turnstile>\<^sub>r R"
  by (rel_auto)

lemma Rel_design: "Rel(P \<turnstile>\<^sub>r Q) = (P \<Rightarrow> Q)"
  by (rel_auto)

interpretation Des_Rel_coretract:
  coretract "\<^bold>H \<Leftarrow>\<langle>Des,Rel\<rangle>\<Rightarrow> id"
  rewrites
    "\<And> x. x \<in> carrier \<X>\<^bsub>\<^bold>H \<Leftarrow>\<langle>Des,Rel\<rangle>\<Rightarrow> id\<^esub> = (x is \<^bold>H)" and
    "\<And> x. x \<in> carrier \<Y>\<^bsub>\<^bold>H \<Leftarrow>\<langle>Des,Rel\<rangle>\<Rightarrow> id\<^esub> = True" and
    "\<pi>\<^sub>*\<^bsub>\<^bold>H \<Leftarrow>\<langle>Des,Rel\<rangle>\<Rightarrow> id\<^esub> = Des" and
    "\<pi>\<^sup>*\<^bsub>\<^bold>H \<Leftarrow>\<langle>Des,Rel\<rangle>\<Rightarrow> id\<^esub> = Rel" and
    "le \<X>\<^bsub>\<^bold>H \<Leftarrow>\<langle>Des,Rel\<rangle>\<Rightarrow> id\<^esub> = (\<sqsubseteq>)" and
    "le \<Y>\<^bsub>\<^bold>H \<Leftarrow>\<langle>Des,Rel\<rangle>\<Rightarrow> id\<^esub> = (\<sqsubseteq>)"
proof (unfold_locales, simp_all)
  show "\<And>x. x is id"
    by (simp add: Healthy_def)
next
  show "Rel \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>id\<rbrakk>\<^sub>H"
    by (auto simp add: Rel_def Healthy_def)
next
  show "Des \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    by (auto simp add: Des_def Healthy_def H1_H2_commute H1_idem H2_idem)
next
  fix R :: "('a, 'b) urel"
  show "R \<sqsubseteq> Rel (Des R)"
    by (simp add: Des_design Rel_design)
next
  fix R :: "('a, 'b) urel" and D :: "('a, 'b) rel_des"
  assume a: "D is \<^bold>H"
  then obtain D\<^sub>1 D\<^sub>2 where D: "D = D\<^sub>1 \<turnstile>\<^sub>r D\<^sub>2"
    by (metis H1_H2_commute H1_H2_is_rdesign H1_idem Healthy_def')
  show "(Rel D \<sqsubseteq> R) = (D \<sqsubseteq> Des R)"
  proof -
    have "(D \<sqsubseteq> Des R) = (D\<^sub>1 \<turnstile>\<^sub>r D\<^sub>2 \<sqsubseteq> true \<turnstile>\<^sub>r R)"
      by (simp add: D Des_design)
    also have "... = `D\<^sub>1 \<and> R \<Rightarrow> D\<^sub>2`"
      by (simp add: rdesign_refinement)
    also have "... = ((D\<^sub>1 \<Rightarrow> D\<^sub>2) \<sqsubseteq> R)"
      by (rel_auto)
    also have "... = (Rel D \<sqsubseteq> R)"
      by (simp add: D Rel_design)
    finally show ?thesis ..
  qed
qed


text \<open>From this interpretation we gain many Galois theorems. Some require simplification to
        remove superfluous assumptions.\<close>

thm Des_Rel_coretract.deflation[simplified]
thm Des_Rel_coretract.inflation
thm Des_Rel_coretract.upper_comp[simplified]
thm Des_Rel_coretract.lower_comp

subsection \<open>Fixed Points\<close>

notation des_theory.utp_lfp ("\<mu>\<^sub>D")
notation des_theory.utp_gfp ("\<nu>\<^sub>D")

notation ndes_theory.utp_lfp ("\<mu>\<^sub>N")
notation ndes_theory.utp_gfp ("\<nu>\<^sub>N")

syntax
  "_dmu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>D _ \<bullet> _" [0, 10] 10)
  "_dnu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>D _ \<bullet> _" [0, 10] 10)
  "_ndmu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>N _ \<bullet> _" [0, 10] 10)
  "_ndnu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>N _ \<bullet> _" [0, 10] 10)

translations
  "\<mu>\<^sub>D X \<bullet> P" == "\<mu>\<^sub>D (\<lambda> X. P)"
  "\<nu>\<^sub>D X \<bullet> P" == "\<nu>\<^sub>D (\<lambda> X. P)"
  "\<mu>\<^sub>N X \<bullet> P" == "\<mu>\<^sub>N (\<lambda> X. P)"
  "\<nu>\<^sub>N X \<bullet> P" == "\<nu>\<^sub>N (\<lambda> X. P)"

thm des_theory.LFP_unfold
thm des_theory.GFP_unfold

text \<open>Specialise @{thm [source] mu_refine_intro} to designs.\<close>

lemma design_mu_refine_intro:
  assumes "$ok\<acute> \<sharp> C" "$ok\<acute> \<sharp> S" "(C \<turnstile> S) \<sqsubseteq> F(C \<turnstile> S)" "`C \<Rightarrow> (\<mu>\<^sub>D F \<Leftrightarrow> \<nu>\<^sub>D F)`"
  shows "(C \<turnstile> S) \<sqsubseteq> \<mu>\<^sub>D F"
proof -
  from assms have "(C \<turnstile> S) \<sqsubseteq> \<nu>\<^sub>D F"
    by (simp add: design_is_H1_H2 des_theory.GFP_upperbound)
  with assms show ?thesis
    by (rel_auto, metis (no_types, lifting))
qed

lemma rdesign_mu_refine_intro:
  assumes "(C \<turnstile>\<^sub>r S) \<sqsubseteq> F(C \<turnstile>\<^sub>r S)" "`\<lceil>C\<rceil>\<^sub>D \<Rightarrow> (\<mu>\<^sub>D F \<Leftrightarrow> \<nu>\<^sub>D F)`"
  shows "(C \<turnstile>\<^sub>r S) \<sqsubseteq> \<mu>\<^sub>D F"
  using assms by (simp add: rdesign_def design_mu_refine_intro unrest)

lemma H1_H2_mu_refine_intro:
  assumes "P is \<^bold>H" "P \<sqsubseteq> F(P)" "`\<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D \<Rightarrow> (\<mu>\<^sub>D F \<Leftrightarrow> \<nu>\<^sub>D F)`"
  shows "P \<sqsubseteq> \<mu>\<^sub>D F"
  by (metis H1_H2_eq_rdesign Healthy_if assms rdesign_mu_refine_intro)

text \<open>Foundational theorem for recursion introduction using a well-founded relation. Contributed
  by Dr. Yakoub Nemouchi.\<close>

theorem rdesign_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Monotonic F"
    and      H: "F \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. (P \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Q \<sqsubseteq> F ((P \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Q)"
  shows "(P \<turnstile>\<^sub>r Q) \<sqsubseteq> \<mu>\<^sub>D F"            
proof -          
  {
  fix st
  have "(P \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Q \<sqsubseteq> \<mu>\<^sub>D F" 
  using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(P \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Q \<sqsubseteq> \<mu>\<^sub>D F"
      by rel_blast
    from M H
    have 1: "\<mu>\<^sub>D F \<sqsubseteq>  F (\<mu>\<^sub>D F)"
      by (simp add: des_theory.LFP_lemma3 mono_Monotone_utp_order)
    from 0 1 have 2:"(P \<and> (\<lceil>e\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Q \<sqsubseteq> F (\<mu>\<^sub>D F)"
      by simp
    have 3: "F ((P \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Q) \<sqsubseteq> F (\<mu>\<^sub>D F)"
      by (simp add: 0 M monoD)
    have 4:"(P \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M des_theory.LFP_lemma2 dual_order.trans mono_Monotone_utp_order
      by (metis (no_types) partial_object.simps(1) utp_order_def)
  qed
  }
  thus ?thesis
    by (pred_simp)
qed  

theorem ndesign_mu_wf_refine_intro': 
  assumes   WF: "wf R"
    and      M: "Monotonic F"
    and      H: "F \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q)"
  shows "(p \<turnstile>\<^sub>n Q) \<sqsubseteq> \<mu>\<^sub>D F"
  using assms unfolding ndesign_def
  by (rule_tac rdesign_mu_wf_refine_intro[of R F "\<lceil>p\<rceil>\<^sub><" e], simp_all add: alpha)

theorem ndesign_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Monotonic F"
    and      H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q)"
  shows "(p \<turnstile>\<^sub>n Q) \<sqsubseteq> \<mu>\<^sub>N F"
proof -          
  {
  fix st
  have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<mu>\<^sub>N F" 
  using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<mu>\<^sub>N F"
      by rel_blast
    from M H des_theory.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>N F \<sqsubseteq>  F (\<mu>\<^sub>N F)"
      by (simp add: mono_Monotone_utp_order ndes_theory.LFP_lemma3)
    from 0 1 have 2:"(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> F (\<mu>\<^sub>N F)"
      by simp
    have 3: "F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> F (\<mu>\<^sub>N F)"
      by (simp add: 0 M monoD)
    have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M ndes_theory.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by (metis (no_types) partial_object.simps(1) utp_order_def)
  qed
  }
  thus ?thesis
    by (pred_simp)
qed  

end