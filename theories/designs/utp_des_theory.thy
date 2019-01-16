subsection {* UTP theory of Designs *}

theory utp_des_theory
  imports utp_des_healths
begin

subsection {* UTP theories *}

typedecl DES
typedecl NDES

abbreviation "DES \<equiv> UTHY(DES, '\<alpha> des)"
abbreviation "NDES \<equiv> UTHY(NDES, '\<alpha> des)"

overloading
  des_hcond == "utp_hcond :: (DES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health"
  des_unit == "utp_unit :: (DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" (unchecked)

  ndes_hcond == "utp_hcond :: (NDES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health"
  ndes_unit == "utp_unit :: (NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" (unchecked)

begin
  definition des_hcond :: "(DES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health" where
  [upred_defs]: "des_hcond t = H1_H2"

  definition des_unit :: "(DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" where
  [upred_defs]: "des_unit t = II\<^sub>D"

  definition ndes_hcond :: "(NDES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health" where
  [upred_defs]: "ndes_hcond t = H1_H3"

  definition ndes_unit :: "(NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" where
  [upred_defs]: "ndes_unit t = II\<^sub>D"

end

interpretation des_utp_theory: utp_theory DES
  by (simp add: H1_H2_commute H1_idem H2_idem des_hcond_def utp_theory_def)

interpretation ndes_utp_theory: utp_theory NDES
  by (simp add: H1_H3_commute H1_idem H3_idem ndes_hcond_def utp_theory.intro)

interpretation des_left_unital: utp_theory_left_unital DES
  apply (unfold_locales)
  apply (simp_all add: des_hcond_def des_unit_def)
  using seq_r_H1_H2_closed apply blast
  apply (simp add: rdesign_is_H1_H2 skip_d_def)
  apply (metis H1_idem H1_left_unit Healthy_def')
done

interpretation ndes_unital: utp_theory_unital NDES
  apply (unfold_locales, simp_all add: ndes_hcond_def ndes_unit_def)
  using seq_r_H1_H3_closed apply blast
  apply (metis H1_rdesign H3_def Healthy_def' design_skip_idem skip_d_def)
  apply (metis H1_idem H1_left_unit Healthy_def')
  apply (metis H1_H3_commute H3_def H3_idem Healthy_def')
done

interpretation design_theory_continuous: utp_theory_continuous DES
  rewrites "\<And> P. P \<in> carrier (uthy_order DES) \<longleftrightarrow> P is \<^bold>H"
  and "carrier (uthy_order DES) \<rightarrow> carrier (uthy_order DES) \<equiv> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
  and "\<lbrakk>\<H>\<^bsub>DES\<^esub>\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<H>\<^bsub>DES\<^esub>\<rbrakk>\<^sub>H \<equiv> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
  and "le (uthy_order DES) = (\<sqsubseteq>)"
  and "eq (uthy_order DES) = (=)"
  by (unfold_locales, simp_all add: des_hcond_def H1_H2_Continuous utp_order_def)
                                                            
interpretation normal_design_theory_continuous: utp_theory_continuous NDES
  rewrites "\<And> P. P \<in> carrier (uthy_order NDES) \<longleftrightarrow> P is \<^bold>N"
  and "carrier (uthy_order NDES) \<rightarrow> carrier (uthy_order NDES) \<equiv> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  and "\<lbrakk>\<H>\<^bsub>NDES\<^esub>\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<H>\<^bsub>NDES\<^esub>\<rbrakk>\<^sub>H \<equiv> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  and "le (uthy_order NDES) = (\<sqsubseteq>)"
  and "A \<subseteq> carrier (uthy_order NDES) \<longleftrightarrow> A \<subseteq> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"  
  and "eq (uthy_order NDES) = (=)"  
  by (unfold_locales, simp_all add: ndes_hcond_def H1_H3_Continuous utp_order_def)

lemma design_lat_top: "\<^bold>\<top>\<^bsub>DES\<^esub> = \<^bold>H(false)"
  by (simp add: design_theory_continuous.healthy_top, simp add: des_hcond_def)

lemma design_lat_bottom: "\<^bold>\<bottom>\<^bsub>DES\<^esub> = \<^bold>H(true)"
  by (simp add: design_theory_continuous.healthy_bottom, simp add: des_hcond_def)

lemma ndesign_lat_top: "\<^bold>\<top>\<^bsub>NDES\<^esub> = \<top>\<^sub>D"
  by (metis (mono_tags, lifting) H1_below_top antisym_conv des_top_is_H1_H3 ndes_hcond_def 
      normal_design_theory_continuous.healthy_top normal_design_theory_continuous.top_higher)

lemma ndesign_lat_bottom: "\<^bold>\<bottom>\<^bsub>NDES\<^esub> = \<^bold>N(true)"
  by (metis ndes_hcond_def normal_design_theory_continuous.healthy_bottom)

interpretation ndes_kleene: utp_theory_kleene "UTHY(NDES, '\<alpha> des)"
  rewrites "\<And> P. P \<in> carrier (uthy_order NDES) \<longleftrightarrow> P is \<^bold>N"
  and "P is \<H>\<^bsub>NDES\<^esub> \<longleftrightarrow> P is \<^bold>N"
  and "carrier (uthy_order NDES) \<rightarrow> carrier (uthy_order NDES) \<equiv> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  and "\<lbrakk>\<H>\<^bsub>NDES\<^esub>\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<H>\<^bsub>NDES\<^esub>\<rbrakk>\<^sub>H \<equiv> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  and "\<^bold>\<top>\<^bsub>NDES\<^esub> = \<top>\<^sub>D"
  and "\<I>\<I>\<^bsub>NDES\<^esub> = II\<^sub>D"
  and "le (uthy_order NDES) = (\<sqsubseteq>)"
  by (unfold_locales, simp_all add: ndesign_lat_top, simp_all add: H1_H3_top_left ndes_hcond_def ndes_unit_def closure)

abbreviation ndes_star :: "_ \<Rightarrow> _"  ("_\<^sup>\<star>\<^sup>D" [999] 999) where
"P\<^sup>\<star>\<^sup>D \<equiv> P\<^bold>\<star>\<^bsub>NDES\<^esub>"

subsection {* Galois Connection *}

text {* Example Galois connection between designs and relations. Based on Jim's example in COMPASS
        deliverable D23.5. *}

definition [upred_defs]: "Des(R) = \<^bold>H(\<lceil>R\<rceil>\<^sub>D \<and> $ok\<acute>)"
definition [upred_defs]: "Rel(D) = \<lfloor>D\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>\<rfloor>\<^sub>D"

lemma Des_design: "Des(R) = true \<turnstile>\<^sub>r R"
  by (rel_auto)

lemma Rel_design: "Rel(P \<turnstile>\<^sub>r Q) = (P \<Rightarrow> Q)"
  by (rel_auto)

interpretation Des_Rel_coretract:
  coretract "DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL"
  rewrites
    "\<And> x. x \<in> carrier \<X>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = (x is \<^bold>H)" and
    "\<And> x. x \<in> carrier \<Y>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = True" and
    "\<pi>\<^sub>*\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = Des" and
    "\<pi>\<^sup>*\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = Rel" and
    "le \<X>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = (\<sqsubseteq>)" and
    "le \<Y>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = (\<sqsubseteq>)"
proof (unfold_locales, simp_all add: rel_hcond_def des_hcond_def)
  show "\<And>x. x is id"
    by (simp add: Healthy_def)
next
  show "Rel \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>id\<rbrakk>\<^sub>H"
    by (auto simp add: Rel_def rel_hcond_def Healthy_def)
next
  show "Des \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    by (auto simp add: Des_def des_hcond_def Healthy_def H1_H2_commute H1_idem H2_idem)
next
  fix R :: "'a hrel"
  show "R \<sqsubseteq> Rel (Des R)"
    by (simp add: Des_design Rel_design)
next
  fix R :: "'a hrel" and D :: "'a hrel_des"
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

text {* From this interpretation we gain many Galois theorems. Some require simplification to
        remove superfluous assumptions. *}

thm Des_Rel_coretract.deflation[simplified]
thm Des_Rel_coretract.inflation
thm Des_Rel_coretract.upper_comp[simplified]
thm Des_Rel_coretract.lower_comp

subsection {* Fixed Points *}

abbreviation design_lfp :: "('\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" ("\<mu>\<^sub>D") where
"\<mu>\<^sub>D F \<equiv> \<^bold>\<mu>\<^bsub>DES\<^esub> F"

abbreviation design_gfp :: "('\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" ("\<nu>\<^sub>D") where
"\<nu>\<^sub>D F \<equiv> \<^bold>\<nu>\<^bsub>DES\<^esub> F"

syntax
  "_dmu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>D _ \<bullet> _" [0, 10] 10)
  "_dnu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>D _ \<bullet> _" [0, 10] 10)

translations
  "\<mu>\<^sub>D X \<bullet> P" == "\<^bold>\<mu>\<^bsub>CONST DES\<^esub> (\<lambda> X. P)"
  "\<nu>\<^sub>D X \<bullet> P" == "\<^bold>\<nu>\<^bsub>CONST DES\<^esub> (\<lambda> X. P)"

thm design_theory_continuous.GFP_unfold
thm design_theory_continuous.LFP_unfold

text {* Specialise @{thm [source] mu_refine_intro} to designs. *}

lemma design_mu_refine_intro:
  assumes "$ok\<acute> \<sharp> C" "$ok\<acute> \<sharp> S" "(C \<turnstile> S) \<sqsubseteq> F(C \<turnstile> S)" "`C \<Rightarrow> (\<mu>\<^sub>D F \<Leftrightarrow> \<nu>\<^sub>D F)`"
  shows "(C \<turnstile> S) \<sqsubseteq> \<mu>\<^sub>D F"
proof -
  from assms have "(C \<turnstile> S) \<sqsubseteq> \<nu>\<^sub>D F"
    thm design_theory_continuous.weak.GFP_upperbound
    by (simp add: design_is_H1_H2 design_theory_continuous.weak.GFP_upperbound)
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

text {* Foundational theorem for recursion introduction using a well-founded relation. Contributed
  by Dr. Yakoub Nemouchi. *}

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
    from M H design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>D F \<sqsubseteq>  F (\<mu>\<^sub>D F)"
      by blast
    from 0 1 have 2:"(P \<and> (\<lceil>e\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Q \<sqsubseteq> F (\<mu>\<^sub>D F)"
      by simp
    have 3: "F ((P \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Q) \<sqsubseteq> F (\<mu>\<^sub>D F)"
      by (simp add: 0 M monoD)
    have 4:"(P \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
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
  shows "(p \<turnstile>\<^sub>n Q) \<sqsubseteq> \<^bold>\<mu>\<^bsub>NDES\<^esub> F"
proof -          
  {
  fix st
  have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<^bold>\<mu>\<^bsub>NDES\<^esub> F" 
  using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<^bold>\<mu>\<^bsub>NDES\<^esub> F"
      by rel_blast
    from M H design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<^bold>\<mu>\<^bsub>NDES\<^esub> F \<sqsubseteq>  F (\<^bold>\<mu>\<^bsub>NDES\<^esub> F)"
      by (simp add: mono_Monotone_utp_order normal_design_theory_continuous.LFP_lemma3)
    from 0 1 have 2:"(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> F (\<^bold>\<mu>\<^bsub>NDES\<^esub> F)"
      by simp
    have 3: "F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> F (\<^bold>\<mu>\<^bsub>NDES\<^esub> F)"
      by (simp add: 0 M monoD)
    have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M normal_design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by (pred_simp)
qed  


end