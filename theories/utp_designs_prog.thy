theory utp_designs_prog
  imports utp_designs
begin

typedef 's ndes = "{P :: 's hrel_des. P is \<^bold>N}"
  by blast
  
setup_lifting type_definition_ndes
    
lift_definition ndes :: "'s upred \<Rightarrow> 's hrel \<Rightarrow> 's ndes" (infixl "\<Turnstile>" 60) is "op \<turnstile>\<^sub>n"
  by (simp add: ndesign_H1_H3)

lift_definition preN :: "'s ndes \<Rightarrow> 's upred" ("pre\<^sub>N") is "\<lambda> P. \<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub><" .
    
lift_definition postN :: "'s ndes \<Rightarrow> 's hrel" ("post\<^sub>N") is "\<lambda> P. post\<^sub>D(P)" .
    
lemma preN_ndes: "pre\<^sub>N(p \<Turnstile> Q) = p"
  by (transfer, simp)

lemma postN_ndes: "post\<^sub>N(p \<Turnstile> Q) = (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> Q)"
  by (simp add: ndes.rep_eq postN.rep_eq)

instantiation ndes :: (type) order
begin
  lift_definition less_eq_ndes :: "'a ndes \<Rightarrow> 'a ndes \<Rightarrow> bool" is "op \<le>" .
  lift_definition less_ndes :: "'a ndes \<Rightarrow> 'a ndes \<Rightarrow> bool" is "op <" .
instance by (intro_classes) (transfer, simp add: less_uexpr_def)+
end
  
instance ndes :: (type) refine ..

instantiation ndes :: (type) complete_lattice
begin
  lift_definition sup_ndes :: "'a ndes \<Rightarrow> 'a ndes \<Rightarrow> 'a ndes" is Lattices.sup
    by (metis (no_types, lifting) H1_H3_commute H1_choice_closed H1_idem H3_def Healthy_def' Healthy_if bounded_semilattice_sup_bot_class.sup_bot.right_neutral upred_semiring.combine_common_factor)
  lift_definition inf_ndes :: "'a ndes \<Rightarrow> 'a ndes \<Rightarrow> 'a ndes" 
    is "\<lambda> P Q. P \<^bold>\<squnion>\<^bsub>NDES\<^esub> Q" by simp
  lift_definition bot_ndes :: "'a ndes" is "\<top>\<^sub>D"
    by (metis H2_not_okay H3_def Healthy_def design_sup_H1_H2_closed design_sup_def design_top_left_zero empty_iff skip_d_alt_def)

  lift_definition top_ndes :: "'a ndes" is "\<bottom>\<^sub>D"
    by (simp add: closure)
  lift_definition Sup_ndes :: "'a ndes set \<Rightarrow> 'a ndes" 
    is "\<lambda> A. \<^bold>\<Sqinter>\<^bsub>NDES\<^esub> A"
    by (rule normal_design_theory_continuous.weak.inf_closed, auto)
  lift_definition Inf_ndes :: "'a ndes set \<Rightarrow> 'a ndes"
    is "\<lambda> A. \<^bold>\<Squnion>\<^bsub>NDES\<^esub> A" 
    by (rule normal_design_theory_continuous.weak.sup_closed, auto)
instance 
  apply (intro_classes)
             apply (transfer, simp add: normal_design_theory_continuous.join_left)
            apply (transfer, simp add: normal_design_theory_continuous.join_right)
           apply (transfer, simp add: normal_design_theory_continuous.join_le)
          apply (transfer, simp add: normal_design_theory_continuous.meet_left)
         apply (transfer, simp add: normal_design_theory_continuous.meet_right)
        apply (transfer, simp add: normal_design_theory_continuous.meet_le)
       apply (transfer, simp add: normal_design_theory_continuous.sup_upper subset_eq)
      apply (transfer, force intro: normal_design_theory_continuous.sup_least)
     apply (transfer, simp add: Ball_Collect normal_design_theory_continuous.inf_lower)
    apply (transfer, force intro: normal_design_theory_continuous.inf_greatest)
   apply (transfer, simp add: ndesign_lat_bottom, metis Healthy_def des_bot_H1_H3)
  apply (transfer, simp add: ndesign_lat_top H1_def H3_def)
done
    
end

abbreviation topN :: "'s ndes" ("\<top>\<^sub>N") where "\<top>\<^sub>N \<equiv> Orderings.top"
abbreviation botN :: "'s ndes" ("\<bottom>\<^sub>N") where "\<bottom>\<^sub>N \<equiv> Orderings.top"
  
lift_definition ndes_skip :: "'s ndes" ("II\<^sub>N") is "II\<^sub>D"
  by (metis assigns_d_H1_H3 assigns_d_id)

lift_definition ndes_assigns :: "'s usubst \<Rightarrow> 's ndes" ("\<langle>_\<rangle>\<^sub>N") is "assigns_d"
  using assigns_d_H1_H3 by auto
    
lift_definition ndes_seq :: "'s ndes \<Rightarrow> 's ndes \<Rightarrow> 's ndes" is "op ;;"
  by (simp add: seq_r_H1_H3_closed)
    
adhoc_overloading
  useq ndes_seq

lemma botN_def: "\<bottom>\<^sub>N = false \<Turnstile> true"
  by (transfer, simp add: ndesign_false_pre)
  
lemma ndes_comp: "(p\<^sub>1 \<Turnstile> P\<^sub>2) ;; (q\<^sub>1 \<Turnstile> Q\<^sub>2) = (p\<^sub>1 \<and> P\<^sub>2 wp q\<^sub>1) \<Turnstile> (P\<^sub>2 ;; Q\<^sub>2)"
  by (metis Rep_ndes_inverse ndes.rep_eq ndes_seq.rep_eq ndesign_composition_wp)
    
lemma ndes_abort_seq: "\<bottom>\<^sub>N ;; P = \<bottom>\<^sub>N"
  by (transfer, metis H1_H3_eq_design Healthy_if design_true_left_zero)
    
lemma preN_abort: "pre\<^sub>N(\<bottom>\<^sub>N) = false"
  by (transfer, rel_auto)
    
lemma postN_abort: "post\<^sub>N(\<bottom>\<^sub>N) = true"
  by (transfer, rel_auto)
   
lemma preN_skip: "pre\<^sub>N(II\<^sub>N) = true"
  by (transfer, simp add: arestr_true skip_d_def)
   
lemma postN_skip: "post\<^sub>N(II\<^sub>N) = II"
  by (transfer, simp add: skip_d_def)
    
lemma preD_ndesign_seq: 
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "pre\<^sub>D (P ;; Q) = (pre\<^sub>D P \<and> \<lceil>post\<^sub>D P wp \<lfloor>pre\<^sub>D Q\<rfloor>\<^sub><\<rceil>\<^sub><)"
proof -
  have "P ;; Q = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) ;; (\<lfloor>pre\<^sub>D(Q)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(Q))"
    by (simp add: assms(1) assms(2) ndesign_form)
  thus ?thesis
    by (simp add: ndesign_composition_wp alpha unrest assms)
qed
  
lemma preD_imp_postD:
  assumes "P is \<^bold>H"
  shows "(pre\<^sub>D(P) \<Rightarrow> post\<^sub>D(P)) = post\<^sub>D(P)"
  by (metis H1_H2_eq_rdesign Healthy_if assms rdesign_post)  
    
lemma postD_ndesign_seq: 
  fixes P Q :: "'\<alpha> hrel_des"
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "post\<^sub>D (P ;; Q) = (pre\<^sub>D P \<and> \<lceil>post\<^sub>D P wp \<lfloor>pre\<^sub>D Q\<rfloor>\<^sub><\<rceil>\<^sub>< \<Rightarrow> post\<^sub>D P ;; post\<^sub>D Q)"
proof -
  have 1: "P ;; Q = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) ;; (\<lfloor>pre\<^sub>D(Q)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(Q))"
    by (simp add: assms(1) assms(2) ndesign_form)
  thus ?thesis
    by (simp add: 1 ndesign_composition_wp alpha unrest assms)
qed
    
lemma preN_seq: "pre\<^sub>N(P ;; Q) = (pre\<^sub>N(P) \<and> post\<^sub>N(P) wp pre\<^sub>N(Q))"
  by (transfer, simp add: preD_ndesign_seq alpha)
    
lemma postN_seq: "post\<^sub>N(P ;; Q) = (\<lceil>pre\<^sub>N(P ;; Q)\<rceil>\<^sub>< \<Rightarrow> (post\<^sub>N(P) ;; post\<^sub>N(Q)))"
  by (transfer, simp add: preD_ndesign_seq postD_ndesign_seq alpha unrest)

    
end