section {* Modelica Core *}

theory Modelica_Core
imports "../hybrid/utp_hrd"
begin
  
text {* Preconditions are captured by negating the continuous divergences, that is the set of
  trajectories that eventually violate the precondition. Every divergence can be extended
  aribtrarily. The precondition effectively states that no trace must violate the precondition
  at the limit. *}
  
definition ModelicaPre ("\<lceil>_\<rceil>\<^sub>M") where
[upred_defs]: "\<lceil>P\<rceil>\<^sub>M = (\<not>\<^sub>r (\<lceil>\<not> P\<rceil>\<^sup>\<rightarrow> ;; true\<^sub>r))"
  
lemma true_ModelicaPre [rpred]: "\<lceil>true\<rceil>\<^sub>M = true\<^sub>r"
  by (rel_auto)

lemma ModelicaPre_RC [closure]: "\<lceil>P\<rceil>\<^sub>M is RC"
  apply (rel_auto)
  apply (meson less_iff minus_gr_zero_iff order_refl)
  apply (metis (no_types, lifting) diff_add_cancel_left' minus_gr_zero_iff order.trans trace_class.add_diff_cancel_left trace_class.add_left_mono)
done

definition ModelicaBlock ("[_ | _]\<^sub>M") where
"[P | Q]\<^sub>M = \<^bold>R\<^sub>s(\<lceil>P\<rceil>\<^sub>M \<turnstile> Q \<diamondop> false)"

lemma preR_simple_block [rdes]: "pre\<^sub>R([P\<^sub>1 | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M) = \<lceil>P\<^sub>1\<rceil>\<^sub>M"
  by (simp add: ModelicaBlock_def preR_rdes closure)

lemma periR_simple_block [rdes]: "peri\<^sub>R([P\<^sub>1 | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M) = (\<lceil>P\<^sub>1\<rceil>\<^sub>M \<Rightarrow>\<^sub>r \<lceil>Q\<^sub>1\<rceil>\<^sub>h)"
  by (simp add: ModelicaBlock_def rdes closure)
  
lemma postR_simple_block [rdes]: "post\<^sub>R([P | \<lceil>Q\<rceil>\<^sub>h]\<^sub>M) = (\<not>\<^sub>r \<lceil>P\<rceil>\<^sub>M)"
  by (simp add: ModelicaBlock_def rdes closure)
    
lemma NSRD_simple_block [closure]: "[P\<^sub>1 | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M is NSRD"
  apply (rule NSRD_intro)
  apply (simp add: ModelicaBlock_def)
  apply (rule RHS_tri_design_is_SRD)
  apply (simp_all add: unrest rdes closure neg_hInt_R1_true)
  apply (metis (no_types, lifting) ModelicaPre_RC R1_seqr_closure rea_not_R1 rea_not_false rea_not_not wpR_RC_false wpR_def)
done
    
end
