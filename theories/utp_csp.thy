(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_csp.thy                                                          *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 31 Jan 2017 *)

section {* Theory of CSP *}

theory utp_csp
  imports utp_rea_designs
begin

subsection {* CSP Alphabet *}

alphabet '\<phi> csp_vars = "'\<sigma> rsp_vars" +
  ref :: "'\<phi> set"

text {*
  The following two locale interpretations are a technicality to improve the
  behaviour of the automatic tactics. They enable (re)interpretation of state
  spaces in order to remove any occurrences of lens types, replacing them by
  tuple types after the tactics @{method pred_simp} and @{method rel_simp}
  are applied. Eventually, it would be desirable to automate preform these
  interpretations automatically as part of the @{command alphabet} command.
*}

interpretation alphabet_csp_prd:
  lens_interp "\<lambda>(ok, wait, tr, m). (ok, wait, tr, ref\<^sub>v m, more m)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_csp_rel:
  lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', m, m').
    (ok, ok', wait, wait', tr, tr', ref\<^sub>v m, ref\<^sub>v m', more m, more m')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

type_synonym ('\<sigma>,'\<phi>) st_csp = "('\<sigma>, '\<phi> list, ('\<phi>, unit) csp_vars_scheme) rsp"
type_synonym ('\<sigma>,'\<phi>) action  = "('\<sigma>,'\<phi>) st_csp hrel"
type_synonym '\<phi> csp = "(unit,'\<phi>) st_csp"
type_synonym '\<phi> rel_csp  = "'\<phi> csp hrel"
  
text {* There is some slight imprecision with the translations, in that we don't bother to check
  if the trace event type and refusal set event types are the same. Essentially this is because
  its very difficult to construct processes where this would be the case. However, it may
  be better to add a proper ML print translation in the future. *}
  
translations
  (type) "('\<sigma>,'\<phi>) st_csp" <= (type) "('\<sigma>, '\<phi> list, '\<phi>1 csp_vars) rsp"
  (type) "('\<sigma>,'\<phi>) action" <= (type) "('\<sigma>, '\<phi>) st_csp hrel"
  
notation csp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>c")
notation csp_vars_child_lens ("\<Sigma>\<^sub>C")

subsection {* Inner Constructs *}
  
text {* CSP Reactive Relations *}
    
definition CRR :: "('s,'e) action \<Rightarrow> ('s,'e) action" where
[upred_defs]: "CRR(P) = (\<exists> $ref \<bullet> RR(P))"

text {* CSP Reactive Conditions *}

definition CRC :: "('s,'e) action \<Rightarrow> ('s,'e) action" where
[upred_defs]: "CRC(P) = (\<exists> $ref \<bullet> RC(P))"

lemma CRR_intro:
  assumes "$ref \<sharp> P" "P is RR"
  shows "P is CRR"
  by (simp add: CRR_def Healthy_def, simp add: Healthy_if assms ex_unrest)
    
lemma CRC_intro:
  assumes "$ref \<sharp> P" "P is RC"
  shows "P is CRC"
  by (simp add: CRC_def Healthy_def, simp add: Healthy_if assms ex_unrest)
    
lemma CRR_implies_RR [closure]: 
  assumes "P is CRR"
  shows "P is RR"
proof -
  have "RR(CRR(P)) = CRR(P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

lemma CRC_implies_RR [closure]: 
  assumes "P is CRC" 
  shows "P is RR"
proof -
  have "RR(CRC(P)) = CRC(P)"
    by (rel_auto)
       (metis (no_types, lifting) Prefix_Order.prefixE Prefix_Order.prefixI append.assoc append_minus)+
  thus ?thesis
    by (metis Healthy_def assms)
qed
  
lemma CRC_implies_RC [closure]: 
  assumes "P is CRC"
  shows "P is RC"
proof -
  have "RC1(CRC(P)) = CRC(P)"
    by (rel_auto, meson dual_order.trans)
  thus ?thesis
    by (simp add: CRC_implies_RR Healthy_if RC1_def RC_intro assms)
qed
  
lemma CRR_unrest_ref [unrest]: "P is CRR \<Longrightarrow> $ref \<sharp> P"
  by (metis CRR_def CRR_implies_RR Healthy_def in_var_uvar ref_vwb_lens unrest_as_exists)
  
lemma CRC_implies_CRR [closure]:
  assumes "P is CRC"
  shows "P is CRR"
  apply (rule CRR_intro)
  apply (simp_all add: unrest assms closure)
  apply (metis CRC_def CRC_implies_RC Healthy_def assms in_var_uvar ref_vwb_lens unrest_as_exists)
done
    
lemma rea_true_CRR [closure]: "true\<^sub>r is CRR"
  by (rel_auto)

lemma rea_true_CRC [closure]: "true\<^sub>r is CRC"
  by (rel_auto)

lemma false_CRR [closure]: "false is CRR"
  by (rel_auto)

lemma false_CRC [closure]: "false is CRC"
  by (rel_auto)

lemma st_cond_CRC [closure]: "[P]\<^sub>S\<^sub>< is CRC"
  by (rel_auto)
    
lemma conj_CRC_closed [closure]:
  "\<lbrakk> P is CRC; Q is CRC \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma disj_CRC_closed [closure]:
  "\<lbrakk> P is CRC; Q is CRC \<rbrakk> \<Longrightarrow> (P \<or> Q) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)
    
lemma shEx_CRR_closed [closure]: 
  assumes "\<And> x. P x is CRR"
  shows "(\<^bold>\<exists> x \<bullet> P(x)) is CRR"
proof -
  have "CRR(\<^bold>\<exists> x \<bullet> CRR(P(x))) = (\<^bold>\<exists> x \<bullet> CRR(P(x)))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms shEx_cong)
qed
    
lemma USUP_ind_CRR_closed [closure]:
  assumes "\<And> i. P i is CRR"
  shows "(\<Squnion> i \<bullet> P(i)) is CRR"
  by (rule CRR_intro, simp_all add: assms unrest closure)

lemma UINF_ind_CRR_closed [closure]:
  assumes "\<And> i. P i is CRR"
  shows "(\<Sqinter> i \<bullet> P(i)) is CRR"
  by (rule CRR_intro, simp_all add: assms unrest closure)
   
lemma cond_tt_CRR_closed [closure]: 
  assumes "P is CRR" "Q is CRR"
  shows "P \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> Q is CRR"
  by (rule CRR_intro, simp_all add: unrest assms closure)
    
lemma rea_implies_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<Rightarrow>\<^sub>r Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma conj_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma disj_CRR_closed [closure]: 
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<or> Q) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)
    
lemma disj_R1_closed [closure]: "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R1"
  by (rel_blast)
    
lemma st_cond_R1_closed [closure]: "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> (P \<triangleleft> b \<triangleright>\<^sub>R Q) is R1"
  by (rel_blast)
    
lemma cond_st_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>R Q) is RR"
  apply (rule RR_intro, simp_all add: unrest closure assms, simp add: Healthy_def R2c_condr)
  apply (simp add: Healthy_if assms RR_implies_R2c)
  apply (rel_auto)
done
    
lemma cond_st_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<triangleleft> b \<triangleright>\<^sub>R Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)
    
definition rea_init :: "_ \<Rightarrow> ('t::trace, 's) uexpr \<Rightarrow> ('s, 't, '\<alpha>, '\<beta>) rel_rsp" ("\<I>'(_,_')") where
[upred_defs]: "\<I>(s,t) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr + \<lceil>t\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u $tr\<acute>)"

lemma unrest_rea_init [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<I>(s,t)"
  by (simp add: rea_init_def unrest lens_indep_sym)

lemma rea_init_R1 [closure]: "\<I>(s,t) is R1"
  apply (rel_auto) using dual_order.trans le_add by blast

lemma rea_init_R2c [closure]: "\<I>(s,t) is R2c"
  apply (rel_auto)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
done

lemma rea_init_R2 [closure]: "\<I>(s,t) is R2"
  by (metis Healthy_def R1_R2c_is_R2 rea_init_R1 rea_init_R2c)
 
lemma csp_init_RR [closure]: "\<I>(s,t) is RR"
  apply (rel_auto)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
  apply (metis le_add less_le less_le_trans)
done

lemma csp_init_CRR [closure]: "\<I>(s,t) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)
    
lemma rea_init_impl_st [closure]: "(\<I>(b,t) \<Rightarrow>\<^sub>r [c]\<^sub>S\<^sub><) is RC"
  apply (rule RC_intro)
  apply (simp add: closure)
  apply (rel_auto)
  using order_trans by auto
    
(*
lemma rea_init_RC1: 
  "\<not>\<^sub>r \<I>(P,t) is RC1"
  apply (rel_auto)
    
lemma rea_init_RC [closure]:
  "\<I>(P,t) is RC"
  by (metis Healthy_def RC_R2_def comp_apply csp_init_RR rea_init_RC1)

lemma rea_init_CRC [closure]:
  "\<I>(P,t) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure) 
*)    

lemma init_acts_empty [rpred]: "\<I>(true,\<langle>\<rangle>) = true\<^sub>r"
  by (rel_auto)
    
lemma rea_not_init [rpred]: 
  "(\<not>\<^sub>r \<I>(P,\<langle>\<rangle>)) = \<I>(\<not>P,\<langle>\<rangle>)"
  by (rel_auto)
       
lemma rea_init_conj [rpred]:
  "(\<I>(P,t) \<and> \<I>(Q,t)) = \<I>(P\<and>Q,t)"
  by (rel_auto)

lemma rea_init_empty_trace [rpred]: "\<I>(s,\<langle>\<rangle>) = [s]\<^sub>S\<^sub><"
  by (rel_auto)
    
lemma rea_init_disj_same [rpred]: "(\<I>(s\<^sub>1,t) \<or> \<I>(s\<^sub>2,t)) = \<I>(s\<^sub>1 \<or> s\<^sub>2, t)"
  by (rel_auto)

lemma rea_init_impl_same [rpred]: "(\<I>(s\<^sub>1,t) \<Rightarrow>\<^sub>r \<I>(s\<^sub>2,t)) = (\<I>(s\<^sub>1, t) \<Rightarrow>\<^sub>r [s\<^sub>2]\<^sub>S\<^sub><)"
  apply (rel_auto) using dual_order.trans le_add by blast+
    
definition trace_subst ("_\<lbrakk>_\<rbrakk>\<^sub>t" [999,0] 999) 
where [upred_defs]: "P\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>&tt-\<lceil>v\<rceil>\<^sub>S\<^sub></&tt\<rbrakk> \<and> $tr + \<lceil>v\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u $tr\<acute>)"

lemma unrest_trace_subst [unrest]:
  "\<lbrakk> mwb_lens x; x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> P\<lbrakk>v\<rbrakk>\<^sub>t"
  by (simp add: trace_subst_def lens_indep_sym unrest)
  
lemma trace_subst_RR_closed [closure]:
  assumes "P is RR"
  shows "P\<lbrakk>v\<rbrakk>\<^sub>t is RR"
proof -
  have "(RR P)\<lbrakk>v\<rbrakk>\<^sub>t is RR"
    apply (rel_auto)
    apply (metis diff_add_cancel_left' trace_class.add_left_mono)
    apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
    using le_add order_trans apply blast
  done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma trace_subst_CRR_closed [closure]:
  assumes "P is CRR"
  shows "P\<lbrakk>v\<rbrakk>\<^sub>t is CRR"
  by (rule CRR_intro, simp_all add: closure assms unrest)
  
lemma tsubst_st_cond [usubst]: "[P]\<^sub>S\<^sub><\<lbrakk>t\<rbrakk>\<^sub>t = \<I>(P,t)"
  by (rel_auto)
    
lemma tsubst_false [usubst]: "false\<lbrakk>y\<rbrakk>\<^sub>t = false"
  by rel_auto
        
lemma tsubst_rea_init [usubst]: "(\<I>(s,x))\<lbrakk>y\<rbrakk>\<^sub>t = \<I>(s,y+x)"
  apply (rel_auto)
  apply (metis add.assoc diff_add_cancel_left' trace_class.add_le_imp_le_left trace_class.add_left_mono)
  apply (metis add.assoc diff_add_cancel_left' le_add trace_class.add_le_imp_le_left trace_class.add_left_mono)+
done

lemma tsubst_rea_not [usubst]: "(\<not>\<^sub>r P)\<lbrakk>v\<rbrakk>\<^sub>t = ((\<not>\<^sub>r P\<lbrakk>v\<rbrakk>\<^sub>t) \<and> \<I>(true,v))"
  apply (rel_auto)
  using le_add order_trans by blast
    
lemma tsubst_true [usubst]: "true\<^sub>r\<lbrakk>v\<rbrakk>\<^sub>t = \<I>(true,v)"
  by (rel_auto)

lemma cond_rea_tt_subst [usubst]:
  "(P \<triangleleft> b \<triangleright>\<^sub>R Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<triangleleft> b \<triangleright>\<^sub>R Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)
        
lemma tsubst_conj [usubst]: "(P \<and> Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<and> Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)

lemma tsubst_disj [usubst]: "(P \<or> Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<or> Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)
    
lemma rea_subst_R1_closed [closure]: "P\<lbrakk>v\<rbrakk>\<^sub>t is R1"
  apply (rel_auto) using le_add order.trans by blast
  
lemma tsubst_UINF_ind [usubst]: "(\<Sqinter> i \<bullet> P(i))\<lbrakk>v\<rbrakk>\<^sub>t = (\<Sqinter> i \<bullet> (P(i))\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)
    
definition csp_enable :: "'s upred \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('e set, 's) uexpr \<Rightarrow> ('s, 'e) action" ("\<E>'(_,_, _')") where
[upred_defs]: "\<E>(s,t,E) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>))"
    
lemma csp_enable_R1_closed [closure]: "\<E>(s,t,E) is R1"
  by (rel_auto)

lemma csp_enable_R2_closed [closure]: "\<E>(s,t,E) is R2c"
  by (rel_auto)
    
lemma csp_enable_RR [closure]: "\<E>(s,t,E) is CRR"
  by (rel_auto)

lemma tsubst_csp_enable [usubst]: "\<E>(s,t\<^sub>2,e)\<lbrakk>t\<^sub>1\<rbrakk>\<^sub>t = \<E>(s,t\<^sub>1^\<^sub>ut\<^sub>2,e)"
  apply (rel_auto)
  apply (metis append.assoc less_eq_list_def prefix_concat_minus)
  apply (simp add: list_concat_minus_list_concat)
done
  
lemma csp_enable_unrests [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<bowtie> ($ref\<acute>)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<E>(s,t,e)"
  by (simp add: csp_enable_def R1_def lens_indep_sym unrest)
    
lemma csp_enable_tr'_eq_tr [rpred]: 
  "\<E>(s,\<langle>\<rangle>,r) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> false = \<E>(s,\<langle>\<rangle>,r)"
  by (rel_auto)
    
lemma csp_enable_st_pred [rpred]: 
  "([s\<^sub>1]\<^sub>S\<^sub>< \<and> \<E>(s\<^sub>2,t,E)) = \<E>(s\<^sub>1 \<and> s\<^sub>2,t,E)"
  by (rel_auto)
      
definition csp_do :: "'s upred \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('s, 'e) action" ("\<Phi>'(_,_,_')") where
[upred_defs]: "\<Phi>(s,\<sigma>,t) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)"
  
lemma unrest_csp_do [unrest]: 
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<bowtie> ($st\<acute>)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<Phi>(s,\<sigma>,t)"
  by (simp_all add: csp_do_def alpha_in_var alpha_out_var prod_as_plus unrest lens_indep_sym)
    
lemma csp_do_CRR [closure]: "\<Phi>(s,\<sigma>,t) is CRR"
  by (rel_auto)
    
lemma trea_subst_csp_do [usubst]:
  "(\<Phi>(s,\<sigma>,t\<^sub>2))\<lbrakk>t\<^sub>1\<rbrakk>\<^sub>t = \<Phi>(s,\<sigma>,t\<^sub>1 ^\<^sub>u t\<^sub>2)"
  apply (rel_auto)
  apply (metis append.assoc less_eq_list_def prefix_concat_minus)
  apply (simp add: list_concat_minus_list_concat)
done

lemma st_subst_csp_do [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<Phi>(s,\<rho>,t) = \<Phi>(\<sigma> \<dagger> s,\<rho> \<circ> \<sigma>,\<sigma> \<dagger> t)"
  by (rel_auto)
      
lemma st_pred_CRR [closure]: "[P]\<^sub>S\<^sub>< is CRR"
  by (rel_auto)
  
lemma csp_init_do [rpred]: "(\<I>(s1,t) \<and> \<Phi>(s2,\<sigma>,t)) = \<Phi>(s1 \<and> s2, \<sigma>, t)"
  by (rel_auto)
    
lemma csp_do_assign [rpred]:
  assumes "P is CRR"
  shows "\<Phi>(s, \<sigma>, t) ;; P = ([s]\<^sub>S\<^sub>< \<and> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,\<sigma>,t) ;; CRR(P) = ([s]\<^sub>S\<^sub>< \<and> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> CRR(P))\<lbrakk>t\<rbrakk>\<^sub>t)"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
            
lemma subst_state_csp_enable [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<E>(s,t\<^sub>2,e) = \<E>(\<sigma> \<dagger> s, \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> e)"
  by (rel_auto)
    
lemma csp_do_assign_enable [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<E>(s\<^sub>2,t\<^sub>2,e) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1^\<^sub>u(\<sigma> \<dagger> t\<^sub>2), (\<sigma> \<dagger> e))"
  by (simp add: rpred closure usubst)

lemma csp_do_assign_do [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<Phi>(s\<^sub>2,\<rho>,t\<^sub>2) = \<Phi>(s\<^sub>1 \<and> (\<sigma> \<dagger> s\<^sub>2), \<rho> \<circ> \<sigma>, t\<^sub>1^\<^sub>u(\<sigma> \<dagger> t\<^sub>2))"
  by (rel_auto)

lemma csp_do_skip [rpred]:
  assumes "P is CRR"
  shows "\<Phi>(true,id,t) ;; P = P\<lbrakk>t\<rbrakk>\<^sub>t"
proof -
  have "\<Phi>(true,id,t) ;; CRR(P) = (CRR P)\<lbrakk>t\<rbrakk>\<^sub>t"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
    
lemma wpR_csp_do_lemma:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><) ;; P = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>$tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub></$tr\<rbrakk>"
  using assms by (rel_auto, meson)
    
lemma wpR_csp_do [wp]:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "P is CRR"
  shows "\<Phi>(s,\<sigma>,t) wp\<^sub>R P = (\<I>(s,t) \<Rightarrow>\<^sub>r (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,\<sigma>,t) wp\<^sub>R CRR(P) = (\<I>(s,t) \<Rightarrow>\<^sub>r (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> CRR(P))\<lbrakk>t\<rbrakk>\<^sub>t)"
    by (rel_blast)
  thus ?thesis 
    by (simp add: assms Healthy_if)
qed
  
lemma wpR_csp_do_skip [wp]:
  fixes Q :: "('\<sigma>, '\<phi>) action"
  assumes "P is CRR"
  shows "\<Phi>(s,id,t) wp\<^sub>R P = (\<I>(s,t) \<Rightarrow>\<^sub>r P\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,id,t) wp\<^sub>R P = \<Phi>(s,id,t) wp\<^sub>R P"
    by (simp add: skip_r_def)
  thus ?thesis by (simp add: wp assms usubst alpha, rel_auto)
qed
  
subsection {* CSP Trace Merge *}

fun tr_par ::
  "'\<theta> set \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list set" where
"tr_par cs [] [] = {[]}" |
"tr_par cs (e # t) [] = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs t []))" |
"tr_par cs [] (e # t) = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs [] t))" |
"tr_par cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
  (if e\<^sub>1 = e\<^sub>2
    then
      if e\<^sub>1 \<in> cs (* \<and> e\<^sub>2 \<in> cs *)
        then {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 t\<^sub>2)
        else
          ({[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))) \<union>
          ({[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))
    else
      if e\<^sub>1 \<in> cs then
        if e\<^sub>2 \<in> cs then {[]}
        else
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)
      else
        if e\<^sub>2 \<in> cs then
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))
        else
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)) \<union>
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))"

subsubsection {* Lifted Trace Merge *}

syntax "_utr_par" ::
  "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(_ \<star>\<^bsub>_\<^esub>/ _)" [100, 0, 101] 100)

text {* The function @{const trop} is used to lift ternary operators. *}

translations
  "t1 \<star>\<^bsub>cs\<^esub> t2" == "(CONST trop) (CONST tr_par) cs t1 t2"

subsubsection {* Trace Merge Lemmas *}

lemma tr_par_empty:
"tr_par cs t1 [] = {takeWhile (\<lambda>x. x \<notin> cs) t1}"
"tr_par cs [] t2 = {takeWhile (\<lambda>x. x \<notin> cs) t2}"
-- {* Subgoal 1 *}
apply (induct t1; simp)
-- {* Subgoal 2 *}
apply (induct t2; simp)
done

lemma tr_par_sym:
"tr_par cs t1 t2 = tr_par cs t2 t1"
apply (induct t1 arbitrary: t2)
-- {* Subgoal 1 *}
apply (simp add: tr_par_empty)
-- {* Subgoal 2 *}
apply (induct_tac t2)
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarsimp)
apply (blast)
done

lemma trace_merge_nil [simp]: "x \<star>\<^bsub>{}\<^sub>u\<^esub> \<langle>\<rangle> = {x}\<^sub>u"
  by (pred_auto, simp_all add: tr_par_empty, metis takeWhile_eq_all_conv)

lemma trace_merge_empty [simp]:
  "(\<langle>\<rangle> \<star>\<^bsub>cs\<^esub> \<langle>\<rangle>) = {\<langle>\<rangle>}\<^sub>u"
  by (rel_auto)

lemma trace_merge_single_empty [simp]:
  "a \<in> cs \<Longrightarrow> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<langle>\<rangle> = {\<langle>\<rangle>}\<^sub>u"
  by (rel_auto)

lemma trace_merge_empty_single [simp]:
  "a \<in> cs \<Longrightarrow> \<langle>\<rangle> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> = {\<langle>\<rangle>}\<^sub>u"
  by (rel_auto)
    
lemma trace_merge_commute: "t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 = t\<^sub>2 \<star>\<^bsub>cs\<^esub> t\<^sub>1"
  by (rel_simp, simp add: tr_par_sym)
   
lemma csp_trace_simps [simp]: 
  "v ^\<^sub>u \<langle>\<rangle> = v" "\<langle>\<rangle> ^\<^sub>u v = v"
  "v + \<langle>\<rangle> = v" "\<langle>\<rangle> + v = v"
  "bop (op #) x xs ^\<^sub>u ys = bop (op #) x (xs ^\<^sub>u ys)"
  by (rel_auto)+
    
subsection {* Healthiness Conditions *}

text {* We here define extra healthiness conditions for CSP processes. *}

abbreviation CSP1 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP1(P) \<equiv> RD1(P)"

abbreviation CSP2 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP2(P) \<equiv> RD2(P)"

abbreviation CSP :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP(P) \<equiv> SRD(P)"

definition STOP :: "'\<phi> rel_csp" where
[upred_defs]: "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition SKIP :: "'\<phi> rel_csp" where
[upred_defs]: "SKIP = \<^bold>R\<^sub>s(\<exists> $ref \<bullet> CSP1(II))"

definition Stop :: "('\<sigma>, '\<phi>) action" where
[upred_defs]: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition Skip :: "('\<sigma>, '\<phi>) action" where
[upred_defs]: "Skip = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st))"

definition CSP3 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "CSP3(P) = (Skip ;; P)"

definition CSP4 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "CSP4(P) = (P ;; Skip)"

definition NCSP :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "NCSP = CSP3 \<circ> CSP4 \<circ> CSP"

subsection {* Healthiness condition properties *}

text {* @{term SKIP} is the same as @{term Skip}, and @{term STOP} is the same as @{term Stop},
  when we consider stateless CSP processes. This is because any reference to the @{term st}
  variable degenerates when the alphabet type coerces its type to be empty. We therefore
  need not consider @{term SKIP} and @{term STOP} actions. *}

theorem SKIP_is_Skip: "SKIP = Skip"
  by (rel_auto)

theorem STOP_is_Stop: "STOP = Stop"
  by (rel_auto)

theorem Skip_UTP_form: "Skip = \<^bold>R\<^sub>s(\<exists> $ref \<bullet> CSP1(II))"
  by (rel_auto)

lemma Skip_is_CSP [closure]:
  "Skip is CSP"
  by (simp add: Skip_def RHS_design_is_SRD unrest)

lemma Skip_RHS_tri_design: 
  "Skip = \<^bold>R\<^sub>s(true \<turnstile> (false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)))"
  by (rel_auto)

lemma Skip_RHS_tri_design' [rdes_def]: 
  "Skip = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (false \<diamondop> \<Phi>(true,id,\<langle>\<rangle>)))"
  by (rel_auto)
    
lemma Stop_is_CSP [closure]:
  "Stop is CSP"
  by (simp add: Stop_def RHS_design_is_SRD unrest)

lemma Stop_RHS_tri_design: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr) \<diamondop> false)"
  by (rel_auto)
    
lemma Stop_RHS_rdes_def [rdes_def]: "Stop = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<E>(true,\<langle>\<rangle>,{}\<^sub>u) \<diamondop> false)"
  by (rel_auto)
    
lemma pre_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
  by (simp add: pre\<^sub>R_def unrest)

lemma peri_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> peri\<^sub>R(P)"
  by (simp add: peri\<^sub>R_def unrest)

lemma post_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> post\<^sub>R(P)"
  by (simp add: post\<^sub>R_def unrest)

lemma cmt_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"
  by (simp add: cmt\<^sub>R_def unrest)

lemma st_lift_unrest_ref' [unrest]: "$ref\<acute> \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)

lemma RHS_design_ref_unrest [unrest]:
  "\<lbrakk>$ref \<sharp> P; $ref \<sharp> Q \<rbrakk> \<Longrightarrow> $ref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q))\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma preR_Skip [rdes]: "pre\<^sub>R(Skip) = true\<^sub>r"
  by (rel_auto)

lemma periR_Skip [rdes]: "peri\<^sub>R(Skip) = false"
  by (rel_auto)
    
lemma postR_Skip [rdes]: "post\<^sub>R(Skip) = \<Phi>(true,id,\<langle>\<rangle>)"
  by (rel_auto)
        
lemma Skip_left_lemma:
  assumes "P is CSP"
  shows "Skip ;; P = \<^bold>R\<^sub>s ((\<forall> $ref \<bullet> pre\<^sub>R P) \<turnstile> (\<exists> $ref \<bullet> cmt\<^sub>R P))"
proof -
  have "Skip ;; P = 
        \<^bold>R\<^sub>s (($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P \<turnstile> 
            ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) ;; peri\<^sub>R P \<diamondop> 
            ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) ;; post\<^sub>R P)"
    by (simp add: SRD_composition_wp csp_do_def alpha rdes closure wp assms rpred C1, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<forall> $ref \<bullet> pre\<^sub>R P) \<turnstile>
                      ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)      
  also have "... = \<^bold>R\<^sub>s ((\<forall> $ref \<bullet> pre\<^sub>R P) \<turnstile> (\<exists> $ref \<bullet> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma Skip_left_unit:
  assumes "P is CSP" "$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
  shows "Skip ;; P = P"
  using assms
  by (simp add: Skip_left_lemma)
     (metis SRD_reactive_design_alt all_unrest cmt_unrest_ref cmt_wait_false ex_unrest pre_unrest_ref pre_wait_false)

lemma CSP3_intro:
  "\<lbrakk> P is CSP; $ref \<sharp> P\<lbrakk>false/$wait\<rbrakk> \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: CSP3_def Healthy_def' Skip_left_unit)

lemma ref_unrest_RHS_design:
  assumes "$ref \<sharp> P" "$ref \<sharp> Q\<^sub>1" "$ref \<sharp> Q\<^sub>2"
  shows "$ref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<^sub>f"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest usubst assms)

lemma CSP3_SRD_intro:
  assumes "P is CSP" "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)"
  shows "P is CSP3"
proof -
  have P: "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
    by (simp add: SRD_reactive_design_alt assms(1) wait'_cond_peri_post_cmt[THEN sym])
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) is CSP3"
    by (rule CSP3_intro, simp add: assms P, simp add: ref_unrest_RHS_design assms)
  thus ?thesis
    by (simp add: P)
qed

lemma Skip_unrest_ref [unrest]: "$ref \<sharp> Skip\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma Skip_unrest_ref' [unrest]: "$ref\<acute> \<sharp> Skip\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma CSP3_iff:
  assumes "P is CSP"
  shows "P is CSP3 \<longleftrightarrow> ($ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>)"
proof
  assume 1: "P is CSP3"
  have "$ref \<sharp> (Skip ;; P)\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: usubst unrest)
  with 1 show "$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
    by (metis CSP3_def Healthy_def)
next
  assume 1:"$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
  show "P is CSP3"
    by (simp add: 1 CSP3_intro assms)
qed

lemma CSP3_unrest_ref [unrest]:
  assumes "P is CSP" "P is CSP3"
  shows "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)"
proof -
  have a:"($ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>)"
    using CSP3_iff assms by blast
  from a show "$ref \<sharp> pre\<^sub>R(P)"
    by (rel_blast)
  from a show "$ref \<sharp> peri\<^sub>R(P)"
    by (rel_auto)
  from a show "$ref \<sharp> post\<^sub>R(P)"
    by (rel_auto)
qed

lemma CSP3_Skip [closure]:
  "Skip is CSP3"
  by (rule CSP3_intro, simp add: Skip_is_CSP, simp add: Skip_def unrest)

lemma CSP3_Stop [closure]:
  "Stop is CSP3"
  by (rule CSP3_intro, simp add: Stop_is_CSP, simp add: Stop_def unrest)

lemma CSP3_Idempotent [closure]: "Idempotent CSP3"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP3_Continuous: "Continuous CSP3"
  by (simp add: Continuous_def CSP3_def seq_Sup_distl)

lemma Skip_right_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
proof -
  have "P ;; Skip = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> post\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st))"
    by (simp add: SRD_composition_wp closure assms wp rdes rpred, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile>
                       ((cmt\<^sub>R P ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)) \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait \<and> $st\<acute> =\<^sub>u $st))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait \<and> $st\<acute> =\<^sub>u $st))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma Skip_right_tri_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R P)))"
proof -
  have "((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)) = ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R P))"
    by (rel_auto)
  thus ?thesis by (simp add: Skip_right_lemma[OF assms])
qed

lemma CSP4_intro:
  assumes "P is CSP" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
          "$st\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>" "$ref\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>"
  shows "P is CSP4"
proof -
  have "CSP4(P) = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (simp add: CSP4_def Skip_right_lemma assms(1))
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (simp add: wpR_def assms(2) rpred closure cond_var_subst_left cond_var_subst_right)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> $st\<acute> \<bullet> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>)))"
    by (simp add: usubst unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> ((cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (simp add: ex_unrest assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by (simp add: cond_var_split)
  also have "... = P"
    by (simp add: SRD_reactive_design_alt assms(1))
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma CSP4_RC_intro:
  assumes "P is CSP" "pre\<^sub>R(P) is RC"
          "$st\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>" "$ref\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>"
  shows "P is CSP4"
proof -
  have "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
    by (metis (no_types, lifting) R1_seqr_closure assms(2) rea_not_R1 rea_not_false rea_not_not wpR_RC_false wpR_def)
  thus ?thesis
    by (simp add: CSP4_intro assms)
qed
      
lemma Skip_srdes_right_unit:
  "(Skip :: ('\<sigma>,'\<phi>) action) ;; II\<^sub>R = Skip"
  by (rdes_eq)

lemma Skip_srdes_left_unit:
  "II\<^sub>R ;; (Skip :: ('\<sigma>,'\<phi>) action) = Skip"
  by (rdes_eq)

lemma CSP4_right_subsumes_RD3: "RD3(CSP4(P)) = CSP4(P)"
  by (metis (no_types, hide_lams) CSP4_def RD3_def Skip_srdes_right_unit seqr_assoc)

lemma CSP4_implies_RD3: "P is CSP4 \<Longrightarrow> P is RD3"
  by (metis CSP4_right_subsumes_RD3 Healthy_def)

lemma CSP4_tri_intro:
  assumes "P is CSP" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))" "$st\<acute> \<sharp> peri\<^sub>R(P)" "$ref\<acute> \<sharp> post\<^sub>R(P)"
  shows "P is CSP4"
  using assms
  by (rule_tac CSP4_intro, simp_all add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst cmt\<^sub>R_def)

lemma CSP4_NSRD_intro:
  assumes "P is NSRD" "$ref\<acute> \<sharp> post\<^sub>R(P)"
  shows "P is CSP4"
  by (simp add: CSP4_tri_intro NSRD_is_SRD NSRD_neg_pre_unit NSRD_st'_unrest_peri assms)

lemma CSP3_commutes_CSP4: "CSP3(CSP4(P)) = CSP4(CSP3(P))"
  by (simp add: CSP3_def CSP4_def seqr_assoc)

lemma NCSP_implies_CSP [closure]: "P is NCSP \<Longrightarrow> P is CSP"
  by (metis (no_types, hide_lams) CSP3_def CSP4_def Healthy_def NCSP_def SRD_idem SRD_seqr_closure Skip_is_CSP comp_apply)

lemma NCSP_elim [RD_elim]: 
  "\<lbrakk> X is NCSP; P(\<^bold>R\<^sub>s(pre\<^sub>R(X) \<turnstile> peri\<^sub>R(X) \<diamondop> post\<^sub>R(X))) \<rbrakk> \<Longrightarrow> P(X)"
  by (simp add: SRD_reactive_tri_design closure)
    
lemma NCSP_implies_CSP3 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP3"
  by (metis (no_types, lifting) CSP3_def Healthy_def' NCSP_def Skip_is_CSP Skip_left_unit Skip_unrest_ref comp_apply seqr_assoc)

lemma NCSP_implies_CSP4 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP4"
  by (metis (no_types, hide_lams) CSP3_commutes_CSP4 Healthy_def NCSP_def NCSP_implies_CSP NCSP_implies_CSP3 comp_apply)

lemma NCSP_implies_RD3 [closure]: "P is NCSP \<Longrightarrow> P is RD3"
  by (metis CSP3_commutes_CSP4 CSP4_right_subsumes_RD3 Healthy_def NCSP_def comp_apply)

lemma NCSP_implies_NSRD [closure]: "P is NCSP \<Longrightarrow> P is NSRD"
  by (simp add: NCSP_implies_CSP NCSP_implies_RD3 SRD_RD3_implies_NSRD)

lemma NCSP_subset_implies_CSP [closure]:
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using NCSP_implies_CSP by blast

lemma NCSP_subset_implies_NSRD [closure]:
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>NSRD\<rbrakk>\<^sub>H"
  using NCSP_implies_NSRD by blast

lemma CSP_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP"
  by (simp add: is_Healthy_subset_member)

lemma CSP3_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: is_Healthy_subset_member)

lemma CSP4_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP4"
  by (simp add: is_Healthy_subset_member)

lemma NCSP_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is NCSP"
  by (simp add: is_Healthy_subset_member)

lemma NCSP_intro:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "P is NCSP"
  by (metis Healthy_def NCSP_def assms comp_eq_dest_lhs)

lemma NCSP_NSRD_intro:
  assumes "P is NSRD" "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)" "$ref\<acute> \<sharp> post\<^sub>R(P)"
  shows "P is NCSP"
  by (simp add: CSP3_SRD_intro CSP4_NSRD_intro NCSP_intro NSRD_is_SRD assms)

lemma CSP4_neg_pre_unit:
  assumes "P is CSP" "P is CSP4"
  shows "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
  by (simp add: CSP4_implies_RD3 NSRD_neg_pre_unit SRD_RD3_implies_NSRD assms(1) assms(2))

lemma NSRD_CSP4_intro:
  assumes "P is CSP" "P is CSP4"
  shows "P is NSRD"
  by (simp add: CSP4_implies_RD3 SRD_RD3_implies_NSRD assms(1) assms(2))

lemma CSP4_st'_unrest_peri [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$st\<acute> \<sharp> peri\<^sub>R(P)"
  by (simp add: NSRD_CSP4_intro NSRD_st'_unrest_peri assms)

lemma CSP4_healthy_form:
  assumes "P is CSP" "P is CSP4"
  shows "P = \<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P))))"
proof -
  have "P = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (metis CSP4_def Healthy_def Skip_right_lemma assms(1) assms(2))
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (metis (no_types, hide_lams) subst_wait'_left_subst subst_wait'_right_subst wait'_cond_def)
  also have "... = \<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P))))"
    by (simp add: wait'_cond_def usubst peri\<^sub>R_def post\<^sub>R_def cmt\<^sub>R_def unrest)
  finally show ?thesis .
qed

lemma CSP4_ref'_unrest_pre [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P) = pre\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P)))))"
    using CSP4_healthy_form assms(1) assms(2) by fastforce
  also have "... = (\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false"
    by (simp add: rea_pre_RHS_design wpR_def usubst unrest
        CSP4_neg_pre_unit R1_rea_not R2c_preR R2c_rea_not assms)
  also have "$ref\<acute> \<sharp> ..."
    by (simp add: wpR_def unrest)
  finally show ?thesis .
qed

lemma CSP4_ref'_unrest_post [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<acute> \<sharp> post\<^sub>R(P)"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P)))))"
    using CSP4_healthy_form assms(1) assms(2) by fastforce
  also have "... = R1 (R2c ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<Rightarrow>\<^sub>r (\<exists> $ref\<acute> \<bullet> post\<^sub>R P)))"
    by (simp add: rea_post_RHS_design usubst unrest wpR_def)
  also have "$ref\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def wpR_def unrest)
  finally show ?thesis .
qed

lemma CSP3_Chaos [closure]: "Chaos is CSP3"
  by (simp add: Chaos_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Chaos [closure]: "Chaos is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest)

lemma NCSP_Chaos [closure]: "Chaos is NCSP"
  by (simp add: NCSP_intro closure) 
    
lemma CSP3_Miracle [closure]: "Miracle is CSP3"
  by (simp add: Miracle_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Miracle [closure]: "Miracle is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest)

lemma NCSP_Miracle [closure]: "Miracle is NCSP"
  by (simp add: NCSP_intro closure) 
    
lemma NCSP_seqr_closure [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P ;; Q is NCSP"
  by (metis (no_types, lifting) CSP3_def CSP4_def Healthy_def' NCSP_implies_CSP NCSP_implies_CSP3
      NCSP_implies_CSP4 NCSP_intro SRD_seqr_closure assms(1) assms(2) seqr_assoc)

lemma R1_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R1_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R2s_notin_ref': "R2s(\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) = (\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (pred_auto)

lemma CSP4_Skip [closure]: "Skip is CSP4"
  apply (rule CSP4_intro, simp_all add: Skip_is_CSP)
  apply (simp_all add: Skip_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest R2c_true)
done

lemma NCSP_Skip [closure]: "Skip is NCSP"
  by (metis CSP3_Skip CSP4_Skip Healthy_def NCSP_def Skip_is_CSP comp_apply)

lemma CSP4_Stop [closure]: "Stop is CSP4"
  apply (rule CSP4_intro, simp_all add: Stop_is_CSP)
  apply (simp_all add: Stop_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest R2c_true)
done

lemma NCSP_Stop [closure]: "Stop is NCSP"
  by (metis CSP3_Stop CSP4_Stop Healthy_def NCSP_def Stop_is_CSP comp_apply)

lemma CSP4_Idempotent: "Idempotent CSP4"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def CSP4_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP4_Continuous: "Continuous CSP4"
  by (simp add: Continuous_def CSP4_def seq_Sup_distr)

lemma preR_Stop [rdes]: "pre\<^sub>R(Stop) = true\<^sub>r"
  by (simp add: Stop_def Stop_is_CSP rea_pre_RHS_design unrest usubst R2c_true)

lemma periR_Stop [rdes]: "peri\<^sub>R(Stop) = \<E>(true,\<langle>\<rangle>,{}\<^sub>u)"
  by (rel_auto)

lemma postR_Stop [rdes]: "post\<^sub>R(Stop) = false"
  by (rel_auto)

lemma cmtR_Stop [rdes]: "cmt\<^sub>R(Stop) = ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)"
  by (rel_auto)

lemma NCSP_Idempotent [closure]: "Idempotent NCSP"
  by (clarsimp simp add: NCSP_def Idempotent_def)
     (metis (no_types, hide_lams) CSP3_Idempotent CSP3_def CSP4_Idempotent CSP4_def Healthy_def Idempotent_def SRD_idem SRD_seqr_closure Skip_is_CSP seqr_assoc)

lemma NCSP_Continuous [closure]: "Continuous NCSP"
  by (simp add: CSP3_Continuous CSP4_Continuous Continuous_comp NCSP_def SRD_Continuous)

lemma preR_CRR [closure]: "P is NCSP \<Longrightarrow> pre\<^sub>R(P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)
  
lemma periR_CRR [closure]: "P is NCSP \<Longrightarrow> peri\<^sub>R(P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)

lemma postR_CRR [closure]: "P is NCSP \<Longrightarrow> post\<^sub>R(P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)
  
lemma unrest_st'_neg_RC [unrest]:
  assumes "P is RR" "P is RC"
  shows "$st\<acute> \<sharp> P"
proof -
  have "P = (\<not>\<^sub>r \<not>\<^sub>r P)"
    by (simp add: closure rpred assms)
  also have "... = (\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r)"
    by (metis Healthy_if RC1_def RC_implies_RC1 assms(2) calculation)
  also have "$st\<acute> \<sharp> ..."
    by (rel_auto)
  finally show ?thesis .
qed
      
lemma unrest_ref'_neg_RC [unrest]:
  assumes "P is RR" "P is RC"
  shows "$ref\<acute> \<sharp> P"
proof -
  have "P = (\<not>\<^sub>r \<not>\<^sub>r P)"
    by (simp add: closure rpred assms)
  also have "... = (\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r)"
    by (metis Healthy_if RC1_def RC_implies_RC1 assms(2) calculation)
  also have "$ref\<acute> \<sharp> ..."
    by (rel_auto)
  finally show ?thesis .
qed
    
lemma NCSP_rdes_intro:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<acute> \<sharp> Q" "$ref\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is NCSP"
  apply (rule NCSP_intro)
  apply (simp_all add: closure assms)
  apply (rule CSP3_SRD_intro)
  apply (simp_all add: rdes closure assms unrest)
  apply (rule CSP4_tri_intro)
  apply (simp_all add: rdes closure assms unrest)
  apply (metis (no_types, lifting) CRC_implies_RC R1_seqr_closure assms(1) rea_not_R1 rea_not_false rea_not_not wpR_RC_false wpR_def)
done
    
lemma NCSP_preR_CRC [closure]:
  assumes "P is NCSP"
  shows "pre\<^sub>R(P) is CRC"
  by (rule CRC_intro, simp_all add: closure assms unrest)
 
subsection {* CSP theories *}

typedecl TCSP

abbreviation "TCSP \<equiv> UTHY(TCSP, ('\<sigma>,'\<phi>) st_csp)"

overloading
  tcsp_hcond   == "utp_hcond :: (TCSP, ('\<sigma>,'\<phi>) st_csp) uthy \<Rightarrow> (('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) health"
begin
  definition tcsp_hcond :: "(TCSP, ('\<sigma>,'\<phi>) st_csp) uthy \<Rightarrow> (('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) health" where
  [upred_defs]: "tcsp_hcond T = NCSP"
end

interpretation csp_theory: utp_theory_continuous "UTHY(TCSP, ('\<sigma>,'\<phi>) st_csp)"
  rewrites "\<And> P. P \<in> carrier (uthy_order TCSP) \<longleftrightarrow> P is NCSP"
  and "P is \<H>\<^bsub>TCSP\<^esub> \<longleftrightarrow> P is NCSP"
  and "carrier (uthy_order TCSP) \<rightarrow> carrier (uthy_order TCSP) \<equiv> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  and "A \<subseteq> carrier (uthy_order TCSP) \<longleftrightarrow> A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  and "le (uthy_order TCSP) = op \<sqsubseteq>"
  by (unfold_locales, simp_all add: tcsp_hcond_def NCSP_Continuous Healthy_Idempotent Healthy_if NCSP_Idempotent)

declare csp_theory.top_healthy [simp del]
declare csp_theory.bottom_healthy [simp del]

lemma csp_bottom_Chaos: "\<^bold>\<bottom>\<^bsub>TCSP\<^esub> = Chaos"
proof -
  have 1: "\<^bold>\<bottom>\<^bsub>TCSP\<^esub> = CSP3 (CSP4 (CSP true))"
    by (simp add: csp_theory.healthy_bottom, simp add: tcsp_hcond_def NCSP_def)
  also have 2:"... = CSP3 (CSP4 Chaos)"
    by (metis srdes_hcond_def srdes_theory_continuous.healthy_bottom)
  also have 3:"... = Chaos"
    by (metis CSP3_Chaos CSP4_Chaos Healthy_def')
  finally show ?thesis .
qed

lemma csp_top_Miracle: "\<^bold>\<top>\<^bsub>TCSP\<^esub> = Miracle"
proof -
  have 1: "\<^bold>\<top>\<^bsub>TCSP\<^esub> = CSP3 (CSP4 (CSP false))"
    by (simp add: csp_theory.healthy_top, simp add: tcsp_hcond_def NCSP_def)
  also have 2:"... = CSP3 (CSP4 Miracle)"
    by (metis srdes_hcond_def srdes_theory_continuous.healthy_top)
  also have 3:"... = Miracle"
    by (metis CSP3_Miracle CSP4_Miracle Healthy_def')
  finally show ?thesis .
qed
  
subsection {* CSP Constructs *}

definition AssignsCSP :: "'\<sigma> usubst \<Rightarrow> ('\<sigma>, '\<phi>) action" ("\<langle>_\<rangle>\<^sub>C") where
[upred_defs]: "AssignsCSP \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S))"

syntax
  "_assigns_csp" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') :=\<^sub>C '(_')")  
  "_assigns_csp" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>C" 90)

translations
  "_assigns_csp xs vs" => "CONST AssignsCSP (_mk_usubst (CONST id) xs vs)"
  "x :=\<^sub>C v" <= "CONST AssignsCSP (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x :=\<^sub>C v" <= "CONST AssignsCSP (CONST subst_upd (CONST id) x v)"
  "x,y :=\<^sub>C u,v" <= "CONST AssignsCSP (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

text {* There are different collections that we would like to assign to, but they all have different
  types and perhaps more importantly different conditions on the update being well defined. For example,
  for a list well-definedness equates to the index being less than the length etc. Thus we here set
  up a polymorphic constant for CSP assignment updates that can be specialised to different types. *}
  
consts
  csp_assign_upd :: "('f \<Longrightarrow> '\<sigma>) \<Rightarrow> ('k, '\<sigma>) uexpr \<Rightarrow> ('v, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action"  
  
definition AssignCSP_list_update :: 
  "('a list \<Longrightarrow> '\<sigma>) \<Rightarrow> (nat, '\<sigma>) uexpr \<Rightarrow> ('a, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs,rdes_def]: "AssignCSP_list_update x k v = \<^bold>R\<^sub>s([k \<in>\<^sub>u dom\<^sub>u(&x)]\<^sub>S\<^sub>< \<turnstile> false \<diamondop> \<Phi>(true,[x \<mapsto>\<^sub>s &x(k \<mapsto> v)\<^sub>u], \<langle>\<rangle>))"
  
definition AssignCSP_pfun_update :: 
  "(('k, 'v) pfun \<Longrightarrow> '\<sigma>) \<Rightarrow> ('k, '\<sigma>) uexpr \<Rightarrow> ('v, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs,rdes_def]: "AssignCSP_pfun_update x k v = \<^bold>R\<^sub>s([k \<in>\<^sub>u dom\<^sub>u(&x)]\<^sub>S\<^sub>< \<turnstile> false \<diamondop> \<Phi>(true,[x \<mapsto>\<^sub>s &x(k \<mapsto> v)\<^sub>u], \<langle>\<rangle>))"

adhoc_overloading
  csp_assign_upd AssignCSP_list_update and csp_assign_upd AssignCSP_pfun_update
  
text {* All different assignment updates have the same syntax; the type resolves which implementation
  to use. *}
  
syntax
  "_csp_assign_upd" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{_[_]} :=\<^sub>C _" [0,0,72] 72)

translations
  "{x[k]} :=\<^sub>C v" == "CONST csp_assign_upd x k v"
  
definition circus_assume ("{_}\<^sub>C") where
[rdes_def]: "{b}\<^sub>C = \<^bold>R\<^sub>s(\<I>(b,\<langle>\<rangle>) \<turnstile> (false \<diamondop> \<Phi>(true,id,\<langle>\<rangle>)))"
  
text {* The CSP weakest fixed-point is obtained simply by precomposing the body with the CSP
  healthiness condition. *}

abbreviation mu_CSP :: "(('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow> ('\<sigma>, '\<phi>) action" ("\<mu>\<^sub>C") where
"\<mu>\<^sub>C F \<equiv> \<mu> (F \<circ> CSP)"

syntax
  "_mu_CSP" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>C _ \<bullet> _" [0, 10] 10)

translations
  "\<mu>\<^sub>C X \<bullet> P" == "CONST mu_CSP (\<lambda> X. P)"

lemma mu_CSP_equiv:
  assumes "Monotonic F" "F \<in> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "(\<mu>\<^sub>R F) = (\<mu>\<^sub>C F)"
  by (simp add: srd_mu_equiv assms comp_def)
    
lemma mu_CSP_unfold:
  "P is CSP \<Longrightarrow> (\<mu>\<^sub>C X \<bullet> P ;; X) = P ;; (\<mu>\<^sub>C X \<bullet> P ;; X)"
  apply (subst gfp_unfold)
  apply (simp_all add: closure Healthy_if)
done
    
definition Guard ::
  "'\<sigma> cond \<Rightarrow>
   ('\<sigma>, '\<phi>) action \<Rightarrow>
   ('\<sigma>, '\<phi>) action" (infixr "&\<^sub>u" 70) where
[upred_defs]: "g &\<^sub>u A = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R(A)) \<turnstile> ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R(A)) \<or> (\<lceil>\<not> g\<rceil>\<^sub>S\<^sub><) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition ExtChoice ::
  "('\<sigma>, '\<phi>) action set \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "ExtChoice A = \<^bold>R\<^sub>s((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<turnstile> ((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R(P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R(P))))"

syntax
  "_ExtChoice" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<box> _\<in>_ \<bullet>/ _)" [0, 0, 10] 10)
  "_ExtChoice_simp" :: "pttrn \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<box> _ \<bullet>/ _)" [0, 10] 10)

translations
  "\<box>P\<in>A \<bullet> B"   \<rightleftharpoons> "CONST ExtChoice ((\<lambda>P. B) ` A)"
  "\<box>P \<bullet> B"     \<rightleftharpoons> "CONST ExtChoice (CONST range (\<lambda>P. B))"

definition extChoice ::
  "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\<box>" 65) where
[upred_defs]: "P \<box> Q \<equiv> ExtChoice {P, Q}"

definition do\<^sub>u ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "do\<^sub>u e = (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>e\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st))"

definition DoCSP :: "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" ("do\<^sub>C") where
[upred_defs]: "DoCSP a = \<^bold>R\<^sub>s(true \<turnstile> do\<^sub>u a)"

definition PrefixCSP ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow>
  ('\<sigma>, '\<phi>) action \<Rightarrow>
  ('\<sigma>, '\<phi>) action" where
[upred_defs]: "PrefixCSP a P = (do\<^sub>C(a) ;; CSP(P))"

abbreviation "OutputCSP c v P \<equiv> PrefixCSP (c\<cdot>v)\<^sub>u P"

abbreviation GuardedChoiceCSP :: "'\<theta> set \<Rightarrow> ('\<theta> \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"GuardedChoiceCSP A P \<equiv> (\<box> x\<in>A \<bullet> PrefixCSP \<guillemotleft>x\<guillemotright> (P(x)))"

syntax
  "_GuardedChoiceCSP" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<^bold>\<rightarrow> _" [0,0,85] 86)

translations
  "\<box> x\<in>A \<^bold>\<rightarrow> P" == "CONST GuardedChoiceCSP A (\<lambda> x. P)"

text {* This version of input prefix is implemented using iterated external choice and so does not
  depend on the existence of local variables. *}

definition InputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
[upred_defs]: "InputCSP c A P = (\<box> x\<in>UNIV \<bullet> A(x) &\<^sub>u PrefixCSP (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u (P x))"

definition InputVarCSP :: "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"InputVarCSP c A x P = InputCSP c A (\<lambda> v. \<langle>[x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>]\<rangle>\<^sub>C) ;; CSP(P)"

definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  ('a \<Longrightarrow> ('\<sigma>, '\<theta>) st_csp) \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow>
  ('\<sigma>, '\<theta>) action" where
"do\<^sub>I c x P = (
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"

subsection {* Syntax and Translations for Prefix *}

syntax
  "_simple_prefix" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>\<rightarrow> _" [81, 80] 80)

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

text {* We next configure a syntax for mixed prefixes. *}

nonterminal prefix_elem' and mixed_prefix'

syntax "_end_prefix" :: "prefix_elem' \<Rightarrow> mixed_prefix'" ("_")

text {* Input Prefix: @{text "\<dots>?(x)"} *}

syntax "_simple_input_prefix" :: "id \<Rightarrow> prefix_elem'"  ("?'(_')")

text {* Input Prefix with Constraint: @{text "\<dots>?(x : P)"} *}

syntax "_input_prefix" :: "id \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> prefix_elem'" ("?'(_ :/ _')")

text {* Output Prefix: @{text "\<dots>![v]e"} *}

text {* A variable name must currently be provided for outputs, too. Fix?! *}

syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")
syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" (".'(_')")

syntax (output) "_output_prefix_pp" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")

syntax
  "_prefix_aux" :: "pttrn \<Rightarrow> logic \<Rightarrow> prefix_elem'"

text {* Mixed-Prefix Action: @{text "c\<dots>(prefix) \<^bold>\<rightarrow> A"} *}

syntax "_mixed_prefix" :: "prefix_elem' \<Rightarrow> mixed_prefix' \<Rightarrow> mixed_prefix'" ("__")

syntax
  "_prefix_action" ::
  "('a, '\<epsilon>) chan \<Rightarrow> mixed_prefix' \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> ('\<sigma>, '\<epsilon>) action"
  ("(__ \<^bold>\<rightarrow>/ _)" [81, 81, 80] 80)

text {* Syntax translations *}

definition lconj :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('b \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<times> 'b \<Rightarrow> '\<alpha> upred)" (infixr "\<and>\<^sub>l" 35)
where [upred_defs]: "(P \<and>\<^sub>l Q) \<equiv> (\<lambda> (x,y). P x \<and> Q y)"

definition outp_constraint (infix "=\<^sub>o" 60) where
[upred_defs]: "outp_constraint v \<equiv> (\<lambda> x. \<guillemotleft>x\<guillemotright> =\<^sub>u v)"

translations
  "_simple_input_prefix x" \<rightleftharpoons> "_input_prefix x true"
  "_mixed_prefix (_input_prefix x P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern x y) ((\<lambda> x. P) \<and>\<^sub>l Q)"
  "_mixed_prefix (_output_prefix P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern _idtdummy y) ((CONST outp_constraint P) \<and>\<^sub>l Q)"
  "_end_prefix (_input_prefix x P)" \<rightharpoonup> "_prefix_aux x (\<lambda> x. P)"
  "_end_prefix (_output_prefix P)" \<rightharpoonup> "_prefix_aux _idtdummy (CONST outp_constraint P)"
  "_prefix_action c (_prefix_aux x P) A" == "(CONST InputCSP) c P (\<lambda>x. A)"

text {* Basic print translations; more work needed *}

translations
  "_simple_input_prefix x" <= "_input_prefix x true"
  "_output_prefix v" <= "_prefix_aux p (CONST outp_constraint v)"
  "_output_prefix u (_output_prefix v)" 
    <= "_prefix_aux p (\<lambda>(x1, y1). CONST outp_constraint u x2 \<and> CONST outp_constraint v y2)"
  "_input_prefix x P" <= "_prefix_aux v (\<lambda>x. P)"
  "x!(v) \<^bold>\<rightarrow> P" <= "CONST OutputCSP x v P"
  
term "x!(1)!(y) \<^bold>\<rightarrow> P"  
term "x?(v) \<^bold>\<rightarrow> P"
term "x?(v:false) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>) \<^bold>\<rightarrow> P"
term "x?(v)!(1) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>)!(2)?(v:true) \<^bold>\<rightarrow> P"

text {* Basic translations for state variable communications *}

syntax
  "_csp_input_var"  :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_:_ \<^bold>\<rightarrow> _" [81, 0, 0, 80] 80)
  "_csp_inputu_var" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_ \<^bold>\<rightarrow> _" [81, 0, 80] 80)

translations
  "c\<^bold>?$x:A \<^bold>\<rightarrow> P" \<rightleftharpoons> "CONST InputVarCSP c x A P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   \<rightharpoonup> "CONST InputVarCSP c x (CONST UNIV) P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   <= "c\<^bold>?$x:true \<^bold>\<rightarrow> P"

text {* Reactive design contracts for CSP/Circus with refusals *}

definition mk_CRD :: "'s upred \<Rightarrow> ('e list \<Rightarrow> 'e set \<Rightarrow> 's upred) \<Rightarrow> ('e list \<Rightarrow> 's hrel) \<Rightarrow> ('s, 'e) action" where
"mk_CRD P Q R = \<^bold>R\<^sub>s([P]\<^sub>S\<^sub>< \<turnstile> [Q x r]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> \<diamondop> [R(x)]\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk>)"

syntax
  "_ref_var" :: "logic"
  "_mk_CRD"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("[_/ \<turnstile> _/ | _]\<^sub>C")

parse_translation {*
let
  fun ref_var_tr [] = Syntax.free "refs"
    | ref_var_tr _  = raise Match;
in
[(@{syntax_const "_ref_var"}, K ref_var_tr)]
end
*}

translations
  "[P \<turnstile> Q | R]\<^sub>C" => "CONST mk_CRD P (\<lambda> _trace_var _ref_var. Q) (\<lambda> _trace_var. R)"
  "[P \<turnstile> Q | R]\<^sub>C" <= "CONST mk_CRD P (\<lambda> x r. Q) (\<lambda> y. R)"
      
subsection {* Closure properties *}

lemma CSP3_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP3"
  apply (auto simp add: CSP3_def Healthy_def seq_Sup_distl)
  apply (rule cong[of Sup])
  apply (simp)
  using image_iff apply force
done

lemma CSP4_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP4"
  apply (auto simp add: CSP4_def Healthy_def seq_Sup_distr)
  apply (rule cong[of Sup])
  apply (simp)
  using image_iff apply force
done
  
lemma NCSP_Sup_closure [closure]: "\<lbrakk> A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> A) is NCSP"
  apply (rule NCSP_intro, simp_all add: closure)
  apply (metis (no_types, lifting) Ball_Collect CSP3_Sup_closure NCSP_implies_CSP3)
  apply (metis (no_types, lifting) Ball_Collect CSP4_Sup_closure NCSP_implies_CSP4)
done

lemma NCSP_SUP_closure [closure]: "\<lbrakk> \<And> i. P(i) is NCSP; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> i\<in>A. P(i)) is NCSP"
  by (metis (mono_tags, lifting) Ball_Collect NCSP_Sup_closure image_iff image_is_empty)

lemma NCSP_cond_srea [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is NCSP"
  by (rule NCSP_NSRD_intro, simp_all add: closure rdes assms unrest)

lemma AssignsCSP_CSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP"
  by (simp add: AssignsCSP_def RHS_tri_design_is_SRD unrest)

lemma AssignsCSP_CSP3 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP3"
  by (rule CSP3_intro, simp add: closure, rel_auto)

lemma AssignsCSP_CSP4 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP4"
  by (rule CSP4_intro, simp add: closure, rel_auto+)

lemma AssignsCSP_NCSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is NCSP"
  by (simp add: AssignsCSP_CSP AssignsCSP_CSP3 AssignsCSP_CSP4 NCSP_intro)
    
lemma preR_AssignsCSP [rdes]: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = true\<^sub>r"
  by (rel_auto)

lemma periR_AssignsCSP [rdes]: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = false"
  by (rel_auto)

lemma postR_AssignsCSP [rdes]: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = \<Phi>(true,\<sigma>,\<langle>\<rangle>)"
  by (rel_auto)

lemma AssignsCSP_rdes_def [rdes_def] : "\<langle>\<sigma>\<rangle>\<^sub>C = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> \<Phi>(true,\<sigma>,\<langle>\<rangle>))"
  by (rel_auto)
    
lemma AssignCSP_conditional:
  assumes "vwb_lens x"
  shows "x :=\<^sub>C e \<triangleleft> b \<triangleright>\<^sub>R x :=\<^sub>C f = x :=\<^sub>C (e \<triangleleft> b \<triangleright> f)" 
  by (rdes_eq cls: assms)
    
lemma R2c_tr_ext: "R2c ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>)"
  by (rel_auto)

lemma AssignCSP_list_update_CSP [closure]:
  "AssignCSP_list_update x k v is CSP"
  by (simp add: AssignCSP_list_update_def RHS_tri_design_is_SRD unrest)
    
lemma preR_AssignCSP_list_update [rdes]: 
  "pre\<^sub>R(AssignCSP_list_update x k v) = [k \<in>\<^sub>u dom\<^sub>u(&x)]\<^sub>S\<^sub><"
  by (rel_auto)

lemma periR_AssignCSP_list_update [rdes]:
  "peri\<^sub>R(AssignCSP_list_update x k v) = [k \<notin>\<^sub>u dom\<^sub>u(&x)]\<^sub>S\<^sub><"
  by (rel_simp)

lemma post_AssignCSP_list_update [rdes]:
  "post\<^sub>R(AssignCSP_list_update x k v) = (\<Phi>(true,[x \<mapsto>\<^sub>s &x(k \<mapsto> v)\<^sub>u],\<langle>\<rangle>) \<triangleleft> k \<in>\<^sub>u dom\<^sub>u(&x) \<triangleright>\<^sub>R R1(true))"
  by (rel_auto) 

lemma AssignCSP_list_update_NCSP [closure]:
  "(AssignCSP_list_update x k v) is NCSP"
proof (rule NCSP_intro)
  show "{x[k]} :=\<^sub>C v is CSP"
    by (simp add: closure)
  show "{x[k]} :=\<^sub>C v is CSP3"
    by (rule CSP3_SRD_intro, simp_all add: csp_do_def closure rdes unrest)
  show "{x[k]} :=\<^sub>C v is CSP4"
    by (rule CSP4_tri_intro, simp_all add: csp_do_def closure rdes unrest, rel_auto)
qed

lemma AssignCSP_pfun_update_CSP [closure]:
  "AssignCSP_pfun_update x k v is CSP"
  by (simp add: AssignCSP_pfun_update_def RHS_tri_design_is_SRD unrest)
    
lemma preR_AssignCSP_pfun_update [rdes]: 
  "pre\<^sub>R(AssignCSP_pfun_update x k v) = [k \<in>\<^sub>u dom\<^sub>u(&x)]\<^sub>S\<^sub><"
  by (rel_auto)

lemma periR_AssignCSP_pfun_update [rdes]:
  "peri\<^sub>R(AssignCSP_pfun_update x k v) = [k \<notin>\<^sub>u dom\<^sub>u(&x)]\<^sub>S\<^sub><"
  by (rel_simp)

lemma post_AssignCSP_pfun_update [rdes]:
  "post\<^sub>R(AssignCSP_pfun_update x k v) = (\<Phi>(true,[x \<mapsto>\<^sub>s &x(k \<mapsto> v)\<^sub>u],\<langle>\<rangle>) \<triangleleft> k \<in>\<^sub>u dom\<^sub>u(&x) \<triangleright>\<^sub>R R1(true))"
  by (rel_auto) 

lemma AssignCSP_pfun_update_NCSP [closure]:
  "(AssignCSP_pfun_update x k v) is NCSP"
proof (rule NCSP_intro)
  show "{x[k]} :=\<^sub>C v is CSP"
    by (simp add: closure)
  show "{x[k]} :=\<^sub>C v is CSP3"
    by (rule CSP3_SRD_intro, simp_all add: csp_do_def closure rdes unrest)
  show "{x[k]} :=\<^sub>C v is CSP4"
    by (rule CSP4_tri_intro, simp_all add: csp_do_def closure rdes unrest, rel_auto)
qed
  
lemma ref_unrest_abs_st [unrest]:
  "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> \<langle>P\<rangle>\<^sub>S"
  "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> \<langle>P\<rangle>\<^sub>S"
  by (rel_simp, auto simp add: des_vars.defs rp_vars.defs)+
  
lemma NCSP_state_srea [closure]: "P is NCSP \<Longrightarrow> state 'a \<bullet> P is NCSP"
  apply (rule NCSP_NSRD_intro)
  apply (simp_all add: closure rdes)
  apply (simp_all add: state_srea_def unrest closure)
done
    
lemma R1_DoAct: "R1(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto)

lemma R2c_DoAct: "R2c(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto)

lemma DoCSP_alt_def: "do\<^sub>C(a) = R3h(CSP1($ok\<acute> \<and> do\<^sub>u(a)))"
  apply (simp add: DoCSP_def RHS_def design_def impl_alt_def  R1_R3h_commute R2c_R3h_commute R2c_disj
                   R2c_not R2c_ok R2c_ok' R2c_and R2c_DoAct R1_disj R1_extend_conj' R1_DoAct)
  apply (rel_auto)
done

lemma DoAct_unrests [unrest]:
  "$ok \<sharp> do\<^sub>u(a)" "$wait \<sharp> do\<^sub>u(a)"
  by (pred_auto)+

lemma DoCSP_RHS_tri [rdes_def]:
  "do\<^sub>C(a) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<diamondop> \<Phi>(true,id,\<langle>a\<rangle>)))"
  by (simp add: DoCSP_def do\<^sub>u_def wait'_cond_def, rel_auto)

lemma CSP_DoCSP [closure]: "do\<^sub>C(a) is CSP"
  by (simp add: DoCSP_def do\<^sub>u_def RHS_design_is_SRD unrest)

lemma preR_DoCSP [rdes]: "pre\<^sub>R(do\<^sub>C(a)) = true\<^sub>r"
  by (simp add: DoCSP_def rea_pre_RHS_design unrest usubst R2c_true)

lemma periR_DoCSP [rdes]: "peri\<^sub>R(do\<^sub>C(a)) = \<E>(true,\<langle>\<rangle>,{a}\<^sub>u)"
  by (rel_auto) 

lemma postR_DoCSP [rdes]: "post\<^sub>R(do\<^sub>C(a)) = \<Phi>(true,id,\<langle>a\<rangle>)"
  by (rel_auto)

lemma CSP3_DoCSP [closure]: "do\<^sub>C(a) is CSP3"
  by (rule CSP3_intro[OF CSP_DoCSP])
     (simp add: DoCSP_def do\<^sub>u_def RHS_def design_def R1_def R2c_def R2s_def R3h_def unrest usubst)

lemma CSP4_DoCSP [closure]: "do\<^sub>C(a) is CSP4"
  by (rule CSP4_tri_intro[OF CSP_DoCSP], simp_all add: preR_DoCSP periR_DoCSP postR_DoCSP unrest)

lemma NCSP_DoCSP [closure]: "do\<^sub>C(a) is NCSP"
  by (metis CSP3_DoCSP CSP4_DoCSP CSP_DoCSP Healthy_def NCSP_def comp_apply)

lemma CSP_PrefixCSP [closure]: "PrefixCSP a P is CSP"
  by (simp add: PrefixCSP_def closure)

lemma CSP3_PrefixCSP [closure]:
  "PrefixCSP a P is CSP3"
  by (metis (no_types, hide_lams) CSP3_DoCSP CSP3_def Healthy_def PrefixCSP_def seqr_assoc)

lemma CSP4_PrefixCSP [closure]:
  assumes "P is CSP" "P is CSP4"
  shows "PrefixCSP a P is CSP4"
  by (metis (no_types, hide_lams) CSP4_def Healthy_def PrefixCSP_def assms(1) assms(2) seqr_assoc)

lemma NCSP_PrefixCSP [closure]:
  assumes "P is NCSP"
  shows "PrefixCSP a P is NCSP"
  by (metis (no_types, hide_lams) CSP3_PrefixCSP CSP3_commutes_CSP4 CSP4_Idempotent CSP4_PrefixCSP
            CSP_PrefixCSP Healthy_Idempotent Healthy_def NCSP_def NCSP_implies_CSP assms comp_apply)

lemma PrefixCSP_type [closure]: "PrefixCSP a \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using CSP_PrefixCSP by blast

lemma PrefixCSP_Continuous [closure]: "Continuous (PrefixCSP a)"
   by (simp add: Continuous_def PrefixCSP_def ContinuousD[OF SRD_Continuous] seq_Sup_distl)

lemma Guard_tri_design:
  "g &\<^sub>u P = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P)))"
proof -
  have "(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R P \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) = (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P))"
    by (rel_auto)
  thus ?thesis by (simp add: Guard_def)
qed
    
lemma Guard_rdes_def [rdes_def]:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "g &\<^sub>u \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) = \<^bold>R\<^sub>s(([g]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (Q \<triangleleft> g \<triangleright>\<^sub>R ($tr\<acute> =\<^sub>u $tr)) \<diamondop> ([g]\<^sub>S\<^sub>< \<and> R))"
  by (simp add: Guard_tri_design rdes assms, rel_auto)
  
lemma CSP_Guard [closure]: "b &\<^sub>u P is CSP"
  by (simp add: Guard_def, rule RHS_design_is_SRD, simp_all add: unrest)

lemma preR_Guard [rdes]: "P is CSP \<Longrightarrow> pre\<^sub>R(b &\<^sub>u P) = ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)"
  by (simp add: Guard_tri_design rea_pre_RHS_design usubst unrest R2c_preR R2c_lift_state_pre
      R2c_rea_impl R1_rea_impl R1_preR Healthy_if, rel_auto)

lemma periR_Guard [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(b &\<^sub>u P) = (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R \<E>(true,\<langle>\<rangle>,{}\<^sub>u))"
proof -
  have "peri\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)))"
    by (simp add: assms Guard_tri_design rea_peri_RHS_design usubst unrest R1_rea_impl R2c_rea_not 
        R2c_rea_impl R2c_preR R2c_periR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr closure
        Healthy_if R1_cond R1_tr'_eq_tr)
  also have "... = ((pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr))"
    by (rel_auto)
  also have "... = (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr))"      
    by (simp add: SRD_peri_under_pre add: unrest closure assms)
  finally show ?thesis
    by rel_auto
qed
      
lemma postR_Guard [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(b &\<^sub>u P) = ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
proof -
  have "post\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P))"
    by (simp add: Guard_tri_design rea_post_RHS_design usubst unrest R2c_rea_not R2c_and R2c_rea_impl
        R2c_preR R2c_postR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr R1_rea_impl R1_extend_conj'
        R1_post_SRD closure assms)
  also have "... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))"
    by (rel_auto)
  also have "... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
    by (simp add: SRD_post_under_pre add: unrest closure assms)
  also have "... = ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
    by (metis CSP_Guard R1_extend_conj R1_post_SRD calculation rea_st_cond_def)      
  finally show ?thesis .
qed
        
lemma CSP3_Guard [closure]:
  assumes "P is CSP" "P is CSP3"
  shows "b &\<^sub>u P is CSP3"
proof -
  from assms have 1:"$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP_Guard CSP3_iff)
  hence "$ref \<sharp> pre\<^sub>R (P\<lbrakk>0/$tr\<rbrakk>)" "$ref \<sharp> pre\<^sub>R P" "$ref \<sharp> cmt\<^sub>R P"
    by (pred_blast)+
  hence "$ref \<sharp> (b &\<^sub>u P)\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP3_iff Guard_def RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest usubst)
  thus ?thesis
    by (metis CSP3_intro CSP_Guard)
qed

lemma CSP4_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>u P is CSP4"
proof (rule CSP4_tri_intro[OF CSP_Guard])
  show "(\<not>\<^sub>r pre\<^sub>R (b &\<^sub>u P)) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R (b &\<^sub>u P))"
  proof -
    have a:"(\<not>\<^sub>r pre\<^sub>R P) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R P)"
      by (simp add: CSP4_neg_pre_unit assms closure)
    have "(\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true = (\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P))"
    proof -
      have 1:"(\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) = ([b]\<^sub>S\<^sub>< \<and> (\<not>\<^sub>r pre\<^sub>R P))"
        by (rel_auto)
      also have 2:"... = ([b]\<^sub>S\<^sub>< \<and> ((\<not>\<^sub>r pre\<^sub>R P) ;; R1 true))"
        by (simp add: a)
      also have 3:"... = (\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true"
        by (rel_auto)
      finally show ?thesis ..
    qed
    thus ?thesis
      by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro closure assms unrest)
  qed
  show "$st\<acute> \<sharp> peri\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro closure assms unrest)
  show "$ref\<acute> \<sharp> post\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard postR_Guard NSRD_CSP4_intro closure assms unrest)
qed

lemma NCSP_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>u P is NCSP"
proof -
  have "P is CSP"
    using NCSP_implies_CSP assms by blast
  then show ?thesis
    by (metis (no_types) CSP3_Guard CSP3_commutes_CSP4 CSP4_Guard CSP4_Idempotent CSP_Guard Healthy_Idempotent Healthy_def NCSP_def assms comp_apply)
qed
  
subsection {* Sequential Process Laws *}

lemma Stop_left_zero:
  assumes "P is CSP"
  shows "Stop ;; P = Stop"
  by (simp add: NSRD_seq_post_false assms NCSP_implies_NSRD NCSP_Stop postR_Stop)

lemma AssignsCSP_id: "\<langle>id\<rangle>\<^sub>C = Skip"
  by (rel_auto)

lemma Guard_rdes_def':
  assumes "$ok\<acute> \<sharp> P"
  shows "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
proof -
  have "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: Guard_def)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or>  \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
     by (simp add: R1_R2c_commute R1_disj R1_extend_conj' R1_idem R2c_and R2c_disj R2c_idem)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: usubst)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r (pre\<^sub>s \<dagger> P)) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>s \<dagger> P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
   finally show ?thesis .
qed

lemma Guard_comp:
  "g &\<^sub>u h &\<^sub>u P = (g \<and> h) &\<^sub>u P"
  by (rule antisym, rel_blast, rel_blast)

lemma Guard_false [simp]: "false &\<^sub>u P = Stop"
  by (simp add: Guard_def Stop_def rpred closure alpha R1_design_R1_pre)

lemma Guard_true [simp]:
  "P is CSP \<Longrightarrow> true &\<^sub>u P = P"
  by (simp add: Guard_def alpha SRD_reactive_design_alt closure rpred)

lemma ExtChoice_rdes:
  assumes "\<And> i. $ok\<acute> \<sharp> P(i)" "A \<noteq> {}"
  shows "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
proof -
  have "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> pre\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))))"
    by (simp add: ExtChoice_def)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: R2c_UINF R2c_condr R1_cond R1_idem R1_R2c_commute R2c_idem R1_UINF assms R1_USUP R2c_USUP)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: usubst)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((R1(R2c(\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: not_UINF R1_UINF R2c_UINF assms)
  also have "... =
        \<^bold>R\<^sub>s ((R2c(\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: R1_design_R1_pre)
  also have "... =
        \<^bold>R\<^sub>s (((\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (metis (no_types, lifting) RHS_design_R2c_pre)
  also have "... =
        \<^bold>R\<^sub>s (([$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> (\<Squnion>i\<in>A \<bullet> P(i))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
  proof -
    from assms have "\<And> i. pre\<^sub>s \<dagger> P(i) = [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> P(i)"
      by (rel_auto)
    thus ?thesis
      by (simp add: usubst)
  qed
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_pre not_UINF)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto, blast+)

  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes [rdes_def]:
  assumes "\<And> i . $ok\<acute> \<sharp> P\<^sub>1(i)" "A \<noteq> {}"
  shows "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
proof -
  have "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: ExtChoice_rdes assms)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: conj_comm)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes_def [rdes_def]:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "ExtChoice A = \<^bold>R\<^sub>s ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<turnstile> (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)))"
proof -
  have "((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P)) =
        (((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P))"
    by (rel_auto)
  also have "... = (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P))"
    by (rel_auto)
  finally show ?thesis
    by (simp add: ExtChoice_def)
qed
  
lemma ExtChoice_empty: "ExtChoice {} = Stop"
  by (simp add: ExtChoice_def cond_def Stop_def)

lemma ExtChoice_single:
  "P is CSP \<Longrightarrow> ExtChoice {P} = P"
  by (simp add: ExtChoice_def usup_and uinf_or SRD_reactive_design_alt cond_idem)

(* Small external choice as an indexed big external choice *)

lemma extChoice_alt_def:
  "P \<box> Q = (\<box>i::nat\<in>{0,1} \<bullet> P \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q)"
  by (simp add: extChoice_def ExtChoice_def, unliteralise, simp)

lemma extChoice_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
proof -
  have "(\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> \<^bold>R\<^sub>s (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> (Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp only: RHS_cond R2c_lit)
  also have "... = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>2)))"
    by (simp add: design_condr)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
    apply (subst ExtChoice_rdes, simp_all add: assms unrest)
    apply unliteralise
    apply (simp add: uinf_or usup_and)
  done
  finally show ?thesis by (simp add: extChoice_alt_def)
qed

lemma extChoice_tri_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
         \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
        \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: extChoice_rdes assms)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: conj_comm)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>
               (((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)) \<diamondop> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma extChoice_rdes_def [rdes_def]:
  assumes "P\<^sub>1 is RR" "Q\<^sub>1 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
         \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
  by (subst extChoice_tri_rdes, simp_all add: assms unrest)
  
lemma CSP_ExtChoice [closure]:
  "ExtChoice A is CSP"
  by (simp add: ExtChoice_def RHS_design_is_SRD unrest)

lemma CSP_extChoice [closure]:
  "P \<box> Q is CSP"
  by (simp add: CSP_ExtChoice extChoice_def)

lemma preR_ExtChoice [rdes]:
  assumes "A \<noteq> {}" "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "pre\<^sub>R(ExtChoice A) = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P))"
proof -
  have "pre\<^sub>R (ExtChoice A) = (R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P))))"
    by (simp add: ExtChoice_def rea_pre_RHS_design usubst unrest)
  also from assms have "... = (R1 (R2c (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(CSP(P))))))"
    by (metis USUP_healthy)
  also from assms have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(CSP(P))))"
    by (rel_auto)
  also from assms have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(P)))"
    by (metis USUP_healthy)
  finally show ?thesis .
qed

lemma preR_ExtChoice' [rdes]:
  assumes "A \<noteq> {}" "\<And> P. P\<in>A \<Longrightarrow> F(P) is CSP"
  shows "pre\<^sub>R(\<box> P\<in>A \<bullet> F(P)) = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R(F(P)))"
  using assms by (subst preR_ExtChoice, auto)

lemma UINF_rea_impl: "(\<Sqinter> P\<in>A \<bullet> F(P) \<Rightarrow>\<^sub>r G(P)) = ((\<Squnion> P\<in>A \<bullet> F(P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> G(P)))"
  by (rel_auto)  

lemma periR_ExtChoice [rdes]:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<noteq> {}"
  shows "peri\<^sub>R(ExtChoice A) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)"
proof -
  have "peri\<^sub>R (ExtChoice A) = peri\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<turnstile>
                                       ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                                       (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: ExtChoice_tri_rdes_def assms closure)

  also have "... = peri\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R (NCSP P)) \<turnstile>
                             ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R (NCSP P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R (NCSP P))) \<diamondop>
                              (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])

  also have "... = R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r
                            (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (NCSP P))
                             \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                            (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (NCSP P))))"
  proof -
    have "(\<Squnion> P\<in>A \<bullet> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s true] \<dagger> pre\<^sub>R (NCSP P))
         = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P))"
      by (rule USUP_cong, simp add: closure usubst unrest assms)
    thus ?thesis
      by (simp add: rea_peri_RHS_design Healthy_Idempotent SRD_Idempotent usubst unrest assms)
  qed
  also have "... = R1 ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r
                       (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (NCSP P))
                          \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                       (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (NCSP P)))"
    by (simp add: R2c_rea_impl R2c_condr R2c_UINF R2c_preR R2c_periR R2c_tr'_minus_tr R2c_USUP closure)
  also have "... = (((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (NCSP P))) 
                      \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                    ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (NCSP P))))"
    by (simp add: R1_rea_impl R1_cond R1_USUP R1_UINF assms Healthy_if closure, rel_auto)
  also have "... = (((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (NCSP P))) 
                      \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                    ((\<Sqinter> P\<in>A \<bullet> pre\<^sub>R (NCSP P) \<Rightarrow>\<^sub>r peri\<^sub>R (NCSP P))))"
    by (simp add: UINF_rea_impl[THEN sym])
  also have "... = (((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (NCSP P))) 
                      \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                    ((\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (NCSP P))))"
    by (simp add: SRD_peri_under_pre closure assms unrest)  
  also have "... = (((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P)) 
                      \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                    ((\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)))"
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])
  finally show ?thesis .
qed
  
lemma periR_ExtChoice' [rdes]:
  assumes "\<And> P. P\<in>A \<Longrightarrow> F(P) is NCSP" "A \<noteq> {}"
  shows "peri\<^sub>R(\<box> P\<in>A \<bullet> F(P)) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(F P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (F P))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (F P))"
  using assms by (subst periR_ExtChoice, auto simp add: closure unrest)

lemma postR_ExtChoice [rdes]:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<noteq> {}"
  shows "post\<^sub>R(ExtChoice A) = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)"
proof -
  have "post\<^sub>R (ExtChoice A) = post\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<turnstile>
                                       ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                                       (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: ExtChoice_tri_rdes_def closure assms)

  also have "... = post\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R (NCSP P)) \<turnstile>
                             ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                              (\<Sqinter> P \<in> A \<bullet> post\<^sub>R (NCSP P))))"
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])

  also have "... = R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (NCSP P))))"
  proof -
    have "(\<Squnion> P\<in>A \<bullet> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s false] \<dagger> pre\<^sub>R (NCSP P))
         = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P))"
      by (rule USUP_cong, simp add: usubst closure unrest assms)
    thus ?thesis
      by (simp add: rea_post_RHS_design Healthy_Idempotent SRD_Idempotent usubst unrest assms)
  qed
  also have "... = R1 ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (NCSP P)))"
    by (simp add: R2c_rea_impl R2c_condr R2c_UINF R2c_preR R2c_postR
                  R2c_tr'_minus_tr R2c_USUP closure)
  also from assms(2) have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (NCSP P)))"
    by (simp add: R1_rea_impl R1_cond R1_USUP R1_UINF assms Healthy_if closure)
  also have "... = (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R (NCSP P) \<Rightarrow>\<^sub>r post\<^sub>R (NCSP P))"
    by (simp add: UINF_rea_impl)
  also have "... = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (NCSP P))"   
    by (simp add: SRD_post_under_pre closure assms unrest)
  finally show ?thesis
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])
qed

lemma postR_ExtChoice' [rdes]:
  assumes "\<And> P. P\<in>A \<Longrightarrow> F(P) is NCSP" "A \<noteq> {}"
  shows "post\<^sub>R(\<box> P\<in>A \<bullet> F(P)) = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R(F(P)))"
  using assms by (subst postR_ExtChoice, auto simp add: closure unrest)

lemma preR_extChoice:
  assumes "P is CSP" "Q is CSP" "$wait\<acute> \<sharp> pre\<^sub>R(P)" "$wait\<acute> \<sharp> pre\<^sub>R(Q)"
  shows "pre\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"
  by (simp add: extChoice_def preR_ExtChoice assms usup_and)

lemma preR_extChoice' [rdes]:
  assumes "P is NCSP" "Q is NCSP"  
  shows "pre\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"  
  by (simp add: preR_extChoice closure assms unrest)
    
lemma periR_extChoice [rdes]:
  assumes "P is NCSP" "Q is NCSP"
  shows "peri\<^sub>R(P \<box> Q) = ((pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow>\<^sub>r peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>R(P) \<or> peri\<^sub>R(Q)))"
  using assms
  by (simp add: extChoice_def, subst periR_ExtChoice, auto simp add: usup_and uinf_or)
  
lemma postR_extChoice [rdes]:
  assumes "P is NCSP" "Q is NCSP"
  shows "post\<^sub>R(P \<box> Q) = (post\<^sub>R(P) \<or> post\<^sub>R(Q))"
  using assms
  by (simp add: extChoice_def, subst postR_ExtChoice, auto simp add: usup_and uinf_or)
    
lemma ExtChoice_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<box> P\<in>A \<bullet> F(P)) = (\<box> P\<in>A \<bullet> G(P))"
  using assms image_cong by force

lemma ref_unrest_ExtChoice:
  assumes
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"
  shows "$ref \<sharp> (ExtChoice A)\<lbrakk>false/$wait\<rbrakk>"
proof -
  have "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P\<lbrakk>0/$tr\<rbrakk>)"
    using assms by (rel_blast)
  with assms show ?thesis
    by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)
qed

lemma CSP4_set_unrest_wait':
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NCSP_implies_NSRD assms by auto
  thus "$wait\<acute> \<sharp> pre\<^sub>R(P)"
    using NSRD_wait'_unrest_pre by blast
qed

lemma CSP4_set_unrest_st':
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NSRD_CSP4_intro assms(1) assms(2) by blast
  thus "$st\<acute> \<sharp> pre\<^sub>R(P)"
    using NSRD_st'_unrest_pre by blast
qed

lemma CSP4_ExtChoice:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  shows "ExtChoice A is CSP4"
proof (cases "A = {}")
  case True thus ?thesis
    by (simp add: ExtChoice_empty Healthy_def CSP4_def, simp add: Skip_is_CSP Stop_left_zero)
next
  case False
  have 1:"(\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (ExtChoice A)) ;;\<^sub>h R1 true) = pre\<^sub>R (ExtChoice A)"
  proof -
    have "\<And> P. P \<in> A \<Longrightarrow> (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R(P))"
      by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_neg_pre_unit assms)
    thus ?thesis
      apply (simp add: False preR_ExtChoice closure CSP4_set_unrest_wait' assms not_UINF seq_UINF_distr not_USUP)
      apply (rule USUP_cong)
      apply (simp add: rpred assms closure)
    done
  qed
  have 2: "$st\<acute> \<sharp> peri\<^sub>R (ExtChoice A)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> pre\<^sub>R(P)"
      by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_st'_unrest_pre assms)
    have b: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> peri\<^sub>R(P)"
      by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_st'_unrest_peri assms)
    from a b show ?thesis
      apply (subst periR_ExtChoice)
      apply (simp_all add: assms closure unrest CSP4_set_unrest_st' CSP4_set_unrest_wait' False) 
    done
  qed
  have 3: "$ref\<acute> \<sharp> post\<^sub>R (ExtChoice A)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> pre\<^sub>R(P)"
      by (simp add: CSP4_ref'_unrest_pre CSP_Healthy_subset_member NCSP_Healthy_subset_member NCSP_implies_CSP4 NCSP_subset_implies_CSP assms)
    have b: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> post\<^sub>R(P)"
      by (simp add: CSP4_ref'_unrest_post CSP_Healthy_subset_member NCSP_Healthy_subset_member NCSP_implies_CSP4 NCSP_subset_implies_CSP assms)
    from a b show ?thesis
      by (subst postR_ExtChoice, simp_all add: assms CSP4_set_unrest_st' CSP4_set_unrest_wait' unrest False)
  qed
  show ?thesis
    by (rule CSP4_tri_intro, simp_all add: 1 2 3 assms closure)
       (metis "1" R1_seqr_closure rea_not_R1 rea_not_not rea_true_R1)
qed

lemma CSP4_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<box> Q is CSP4"
  by (simp add: extChoice_def, rule CSP4_ExtChoice, simp_all add: assms)

lemma NCSP_ExtChoice [closure]:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  shows "ExtChoice A is NCSP"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: ExtChoice_empty closure)
next
  case False
  show ?thesis
  proof (rule NCSP_intro)
    from assms have cls: "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
      using NCSP_implies_CSP NCSP_implies_CSP3 NCSP_implies_CSP4 by blast+
    have wu: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
      using NCSP_implies_NSRD NSRD_wait'_unrest_pre assms by force
    show 1:"ExtChoice A is CSP"
      by (metis (mono_tags) Ball_Collect CSP_ExtChoice NCSP_implies_CSP assms)
    from cls show "ExtChoice A is CSP3"
      by (rule_tac CSP3_SRD_intro, simp_all add: CSP_Healthy_subset_member CSP3_Healthy_subset_member closure rdes unrest wu assms 1 False) 
    from cls show "ExtChoice A is CSP4"
      by (simp add: CSP4_ExtChoice assms)
  qed
qed

lemma NCSP_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<box> Q is NCSP"
  by (simp add: NCSP_ExtChoice assms extChoice_def)

lemma ExtChoice_comm:
  "P \<box> Q = Q \<box> P"
  by (unfold extChoice_def, simp add: insert_commute)

lemma ExtChoice_idem:
  "P is CSP \<Longrightarrow> P \<box> P = P"
  by (unfold extChoice_def, simp add: ExtChoice_single)

lemma ExtChoice_assoc:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> Q \<box> R = P \<box> (Q \<box> R)"
proof -
  have "P \<box> Q \<box> R = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R))"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
            ((cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) )
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (simp add: conj_assoc disj_assoc)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> (\<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = P \<box> (Q \<box> R)"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  finally show ?thesis .
qed

lemma ExtChoice_Stop:
  assumes "Q is CSP"
  shows "Stop \<box> Q = Q"
  using assms
proof -
  have "Stop \<box> Q = \<^bold>R\<^sub>s (true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Stop_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> ((($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<or> cmt\<^sub>R Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> cmt\<^sub>R Q))"
    by (metis (no_types, lifting) cond_def eq_upred_sym neg_conj_cancel1 utp_pred_laws.inf.left_idem)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> cmt\<^sub>R Q)"
    by (simp add: cond_idem)
  also have "... = Q"
    by (simp add: SRD_reactive_design_alt assms)
  finally show ?thesis .
qed

lemma ExtChoice_Chaos:
  assumes "Q is CSP"
  shows "Chaos \<box> Q = Chaos"
proof -
  have "Chaos \<box> Q = \<^bold>R\<^sub>s (false \<turnstile> true) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Chaos_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> true))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> true)"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = Chaos"
    by (simp add: Chaos_def)
  finally show ?thesis .
qed
  
lemma rea_impl_conj [rpred]: 
  "(P \<Rightarrow>\<^sub>r Q \<Rightarrow>\<^sub>r R) = ((P \<and> Q) \<Rightarrow>\<^sub>r R)"
  by (rel_auto)
               
lemma Guard_conditional:
  assumes "P is NCSP"
  shows "b &\<^sub>u P = P \<triangleleft> b \<triangleright>\<^sub>R Stop"  
  by (rdes_eq cls: assms)
    
lemma Conditional_as_Guard:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q = b &\<^sub>u P \<box> (\<not> b) &\<^sub>u Q"  
  by (rdes_eq cls: assms)
    
lemma InputCSP_CSP [closure]: "x?(v:A(v)) \<^bold>\<rightarrow> P(v) is CSP"
  by (simp add: CSP_ExtChoice InputCSP_def)

lemma InputCSP_NCSP [closure]: "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> x?(v:A(v)) \<^bold>\<rightarrow> P(v) is NCSP"
  apply (simp add: InputCSP_def)
  apply (rule NCSP_ExtChoice)
  apply (simp add: NCSP_Guard NCSP_PrefixCSP image_Collect_subsetI top_set_def)
done

lemma PrefixCSP_RHS_tri_lemma1:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)"
  by (rel_auto)

lemma PrefixCSP_RHS_tri_lemma2:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<and> \<not> $wait\<acute>) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson, fastforce)

lemma PrefixCSP_RHS_tri_lemma3:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson)

lemma tr_extend_seqr:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
  using assms by (simp add: PrefixCSP_RHS_tri_lemma3 assms unrest ex_unrest)
       
(*    
lemma unrest_rea_subst [unrest]: 
  "\<lbrakk> mwb_lens x; x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<sharp> v; x \<sharp> P \<rbrakk> \<Longrightarrow>  x \<sharp> P\<lbrakk>v\<rbrakk>\<^sub>t"
  by (simp add: rea_subst_def R1_def unrest lens_indep_sym)
*)
 
lemma preR_R2 [closure]: "P is SRD \<Longrightarrow> pre\<^sub>R(P) is R2"
  by (metis Healthy_def' R1_preR R2_R2c_def R2c_preR)  

lemma periR_R2 [closure]: "P is SRD \<Longrightarrow> peri\<^sub>R(P) is R2"
  by (simp add: Healthy_def' R1_R2c_peri_RHS R2_R2c_def)
    
lemma postR_R2 [closure]: "P is SRD \<Longrightarrow> post\<^sub>R(P) is R2"
  by (simp add: Healthy_def' R1_R2c_post_RHS R2_R2c_def)

(*
    
lemma tr_extend_seqr' [rdes]:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P" "P is R2"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = undefined"
proof -
  have "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (simp add: tr_extend_seqr assms)
  also have "... = (R2 P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"   
    by (simp add: Healthy_if assms)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (simp add: R2_form)
  also have "... = undefined"      
    apply (simp add: usubst)
*)

(* Can the following double negation be simplified? *)
   
lemma "R1((\<not>\<^sub>r P)\<lbrakk>e/&tt\<rbrakk>) = R1(\<not>\<^sub>r P\<lbrakk>e/&tt\<rbrakk>)"
  by (rel_auto)
  
lemma "R1((P \<Rightarrow>\<^sub>r Q)\<lbrakk>e/&tt\<rbrakk>) = (R1(P\<lbrakk>e/&tt\<rbrakk>) \<Rightarrow>\<^sub>r R1(Q\<lbrakk>e/&tt\<rbrakk>))"
  by (rel_auto)
  
lemma wpR_DoCSP:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P = 
         (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  by (simp add: wpR_def PrefixCSP_RHS_tri_lemma3 unrest usubst ex_unrest assms closure)    
    
lemma wpR_DoCSP_alt:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P = 
         ($tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<Rightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"  
  by (simp add: wpR_DoCSP assms rea_not_def R1_def usubst unrest, rel_auto)
          
lemma trace_ext_R1_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>$tr ^\<^sub>u e/$tr\<rbrakk> is R1"
  by (rel_blast)
      
lemma id_st_subst [usubst]: "\<lceil>id\<rceil>\<^sub>S\<^sub>\<sigma> = id"
  by (pred_auto)
    
lemma preR_PrefixCSP_NCSP [rdes]:
  assumes "P is NCSP"
  shows "pre\<^sub>R(PrefixCSP a P) = (\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  by (simp add: PrefixCSP_def assms closure rdes rpred Healthy_if wp usubst unrest)

lemma csp_enable_tr_empty: "\<E>(true,\<langle>\<rangle>,{v}\<^sub>u) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>v\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (rel_auto)
  
lemma periR_PrefixCSP [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(PrefixCSP a P) = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> (peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
proof -
  have "peri\<^sub>R(PrefixCSP a P) =  peri\<^sub>R (do\<^sub>C a ;; P)"
    by (simp add: PrefixCSP_def closure assms Healthy_if)
  also have "... = ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<Rightarrow>\<^sub>r $tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (simp add: assms NSRD_CSP4_intro csp_enable_tr_empty closure rdes unrest ex_unrest usubst rpred wp)
  also have "... = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<Rightarrow>\<^sub>r peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t))"
    by (rel_auto)
  also have "... = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> ((pre\<^sub>R(P) \<Rightarrow>\<^sub>r peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t))"
    by (rel_auto)
  also have "... = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> (peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"      
    by (simp add: SRD_peri_under_pre assms closure unrest)
  finally show ?thesis .
qed
  
lemma postR_PrefixCSP [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(PrefixCSP a P) = (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t"
proof -
  have "post\<^sub>R(PrefixCSP a P) = ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<Rightarrow>\<^sub>r (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (simp add: PrefixCSP_def assms Healthy_if) 
       (simp add: assms Healthy_if wp closure rdes rpred PrefixCSP_RHS_tri_lemma3 unrest  ex_unrest usubst)
  also have "... = (\<I>(true,\<langle>a\<rangle>) \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (rel_auto)
  also have "... = (\<I>(true,\<langle>a\<rangle>) \<and> (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"      
    by (simp add: SRD_post_under_pre assms closure unrest)
  also have "... = (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t"
    by (rel_auto)
  finally show ?thesis .
qed
      
lemma PrefixCSP_RHS_tri:
  assumes "P is NCSP"
  shows "PrefixCSP a P = \<^bold>R\<^sub>s ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<turnstile> (\<E>(true,\<langle>\<rangle>, {a}\<^sub>u) \<or> peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<diamondop> post\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  by (simp add: PrefixCSP_def Healthy_if unrest assms closure NSRD_composition_wp rdes rpred usubst wp)

text {* For prefix, we can chose whether to propagate the assumptions or not, hence there
  are two laws. *}
    
lemma PrefixCSP_rdes_def_1 [rdes_def]:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<acute> \<sharp> Q" "$ref\<acute> \<sharp> R"
  shows "PrefixCSP a (\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<turnstile> (\<E>(true,\<langle>\<rangle>, {a}\<^sub>u) \<or> Q\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<diamondop> R\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  apply (subst PrefixCSP_RHS_tri)
  apply (rule NCSP_rdes_intro)
  apply (simp_all add: assms rdes closure)
  apply (rel_auto)
done

lemma PrefixCSP_rdes_def_2:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<acute> \<sharp> Q" "$ref\<acute> \<sharp> R"
  shows "PrefixCSP a (\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<turnstile> (\<E>(true,\<langle>\<rangle>, {a}\<^sub>u) \<or> (P\<and>Q)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<diamondop> (P\<and>R)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  apply (subst PrefixCSP_RHS_tri)
  apply (rule NCSP_rdes_intro)
  apply (simp_all add: assms rdes closure)
  apply (rel_auto)
done
    
lemma preR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "pre\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) = (\<Squnion> v \<bullet> [A(v)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r (pre\<^sub>R (P(v)))\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
  by (simp add: InputCSP_def rdes closure assms alpha usubst unrest)
    
lemma periR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "peri\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) =
           ((\<Squnion> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<E>(true, \<langle>\<rangle>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u))) 
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
            (\<Sqinter> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<and> (peri\<^sub>R (P x))\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)" 
  by (simp add: InputCSP_def rdes closure assms, rel_auto)

lemma postR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "post\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) =
          (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> post\<^sub>R (P x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
  using assms by (simp add: InputCSP_def rdes closure assms usubst unrest)

lemma InputCSP_rdes_def [rdes_def]:
  assumes "\<And> v. P(v) is CRC" "\<And> v. Q(v) is CRR" "\<And> v. R(v) is CRR"
          "\<And> v. $st\<acute> \<sharp> Q(v)" "\<And> v. $ref\<acute> \<sharp> R(v)"
  shows "a?(v:A(v)) \<^bold>\<rightarrow> (\<^bold>R\<^sub>s(P(v) \<turnstile> Q(v) \<diamondop> R(v))) = 
         \<^bold>R\<^sub>s( (\<Squnion> v \<bullet> ([A(v)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r (P v)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))
           \<turnstile> (((\<Squnion> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<E>(true, \<langle>\<rangle>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u))) 
               \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
               (\<Sqinter> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<and> (P x \<and> Q x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))
           \<diamondop> (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<and> R x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))" (is "?lhs = ?rhs")
proof -
  have 1:"pre\<^sub>R(?lhs) = (\<Squnion> v \<bullet> [A v]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r P v\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)" (is "_ = ?A")
    by (simp add: rdes NCSP_rdes_intro assms conj_comm closure)
  have 2:"peri\<^sub>R(?lhs) = (\<Squnion> x \<bullet> [A x]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<E>(true,\<langle>\<rangle>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<Rightarrow>\<^sub>r Q x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
    (is "_ = ?B")
    by (simp add: rdes NCSP_rdes_intro assms closure)
  have 3:"post\<^sub>R(?lhs) = (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<Rightarrow>\<^sub>r R x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
    (is "_ = ?C")
    by (simp add: rdes NCSP_rdes_intro assms closure)
  have "?lhs = \<^bold>R\<^sub>s(?A \<turnstile> ?B \<diamondop> ?C)"
    by (subst SRD_reactive_tri_design[THEN sym], simp_all add: closure 1 2 3)
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed
  
(*
lemma InputCSP_RHS_tri [rdes_def]:
  assumes "\<And> v. P(v) is NCSP"
  shows "a?(v:A(v)) \<^bold>\<rightarrow> P(v) =
        \<^bold>R\<^sub>s((\<Squnion> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R (P v)\<lbrakk>$tr ^\<^sub>u \<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)

          \<turnstile>  ((\<Squnion> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow> ((a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R (P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>))
               \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
              (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (peri\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))

          \<diamondop> (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (post\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))"
*)

lemma outp_constraint_prod:
  "(outp_constraint \<guillemotleft>a\<guillemotright> x \<and> outp_constraint \<guillemotleft>b\<guillemotright> y) =
    outp_constraint \<guillemotleft>(a, b)\<guillemotright> (x, y)"
  by (simp add: outp_constraint_def, pred_auto)
  
lemma subst_outp_constraint [usubst]:
  "\<sigma> \<dagger> (v =\<^sub>o x) =  (\<sigma> \<dagger> v =\<^sub>o x)"
  by (rel_auto)
    
lemma UINF_one_point_simp [rpred]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> x \<bullet> [\<guillemotleft>i\<guillemotright> =\<^sub>o x]\<^sub>S\<^sub>< \<and> P(x)) = P(i)"
  by (rel_blast)

lemma USUP_one_point_simp [rpred]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Squnion> x \<bullet> [\<guillemotleft>i\<guillemotright> =\<^sub>o x]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P(x)) = P(i)"
  by (rel_blast)
    
text {* Proofs that the input constrained parser versions of output is the same as the regular definition. *}

lemma output_prefix_is_OutputCSP [simp]:
  assumes "A is NCSP"
  shows "x!(P) \<^bold>\<rightarrow> A = OutputCSP x P A" (is "?lhs = ?rhs")
  by (rule SRD_eq_intro, simp_all add: assms closure rdes, rel_auto+)

lemma OutputCSP_pair_simp [simp]:
  "P is NCSP \<Longrightarrow> a.(\<guillemotleft>i\<guillemotright>).(\<guillemotleft>j\<guillemotright>) \<^bold>\<rightarrow> P = OutputCSP a \<guillemotleft>(i,j)\<guillemotright> P"
  using output_prefix_is_OutputCSP[of "P" a]
  by (simp add: outp_constraint_prod lconj_def InputCSP_def closure del: output_prefix_is_OutputCSP)
    
lemma OutputCSP_triple_simp [simp]:
  "P is NCSP \<Longrightarrow> a.(\<guillemotleft>i\<guillemotright>).(\<guillemotleft>j\<guillemotright>).(\<guillemotleft>k\<guillemotright>) \<^bold>\<rightarrow> P = OutputCSP a \<guillemotleft>(i,j,k)\<guillemotright> P"
  using output_prefix_is_OutputCSP[of "P" a]
  by (simp add: outp_constraint_prod lconj_def InputCSP_def closure del: output_prefix_is_OutputCSP)
    
text {* Useful laws for reducing assignments and identities within peri and postconditions *}
  
lemma tr_extend_seqr_lit [rdes]:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle>/$tr\<rbrakk>"
  using assms by (rel_auto, meson)

lemma tr_assign_comp [rdes]:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S) ;; P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"
  using assms by (rel_auto, meson)    
    
lemma extChoice_Dist:
  assumes "P is CSP" "S \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "S \<noteq> {}"
  shows "P \<box> (\<Sqinter> S) = (\<Sqinter> Q\<in>S. P \<box> Q)"
proof -
  let ?S1 = "pre\<^sub>R ` S" and ?S2 = "cmt\<^sub>R ` S"
  have "P \<box> (\<Sqinter> S) = P \<box> (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: SRD_as_reactive_design[THEN sym] Healthy_SUPREMUM UINF_as_Sup_collect assms)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s((\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q)) \<turnstile> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))"
    by (simp add: RHS_design_USUP SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R(P) \<and> (\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q))) \<turnstile>
                       ((cmt\<^sub>R(P) \<and> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))
                         \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
                        (cmt\<^sub>R(P) \<or> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion> Q\<in>S \<bullet> pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                       (\<Sqinter> Q\<in>S \<bullet> (cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q)))"
    by (simp add: conj_USUP_dist conj_UINF_dist disj_UINF_dist cond_UINF_dist assms)
  also have "... = (\<Sqinter> Q \<in> S \<bullet> \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                                  ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q))))"
    by (simp add: assms RHS_design_USUP)
  also have "... = (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = (\<Sqinter> Q\<in>S. P \<box> CSP(Q))"
    by (simp add: UINF_as_Sup_collect, metis (no_types, lifting) Healthy_if SRD_as_reactive_design assms(1))
  also have "... = (\<Sqinter> Q\<in>S. P \<box> Q)"
    by (rule SUP_cong, simp_all add: Healthy_subset_member[OF assms(2)])
  finally show ?thesis .
qed

lemma extChoice_dist:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> (Q \<sqinter> R) = (P \<box> Q) \<sqinter> (P \<box> R)"
  using assms extChoice_Dist[of P "{Q, R}"] by simp

lemma GuardedChoiceCSP [rdes_def]:
  assumes "\<And> x. P(x) is NCSP" "A \<noteq> {}"
  shows "(\<box> x\<in>A \<^bold>\<rightarrow> P(x)) =
             \<^bold>R\<^sub>s ((\<Squnion> x \<in> A \<bullet> \<I>(true,\<langle>\<guillemotleft>x\<guillemotright>\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R (P x)\<lbrakk>\<langle>\<guillemotleft>x\<guillemotright>\<rangle>\<rbrakk>\<^sub>t) \<turnstile>
                 ((\<Squnion> x \<in> A \<bullet> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>x\<guillemotright>}\<^sub>u)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> x \<in> A \<bullet> peri\<^sub>R (P x)\<lbrakk>\<langle>\<guillemotleft>x\<guillemotright>\<rangle>\<rbrakk>\<^sub>t)) \<diamondop>
                  (\<Sqinter> x \<in> A \<bullet> post\<^sub>R (P x)\<lbrakk>\<langle>\<guillemotleft>x\<guillemotright>\<rangle>\<rbrakk>\<^sub>t))"
  by (simp add: PrefixCSP_RHS_tri assms ExtChoice_tri_rdes closure unrest, rel_auto)

(*
lemma wpR_thing [wp]:
  assumes "\<And> a. P(a) is NCSP"
  shows "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R (pre\<^sub>R (P(last\<^sub>u($tr))))) = (pre\<^sub>R(P last\<^sub>u($tr)))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<not> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; (\<not> pre\<^sub>R (P last\<^sub>u($tr))))"
    by (simp add: wpR_def R1_neg_preR closure assms)
  also have "... = (\<not> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; (\<exists> $ref \<bullet> (\<not> pre\<^sub>R (P last\<^sub>u($tr)))))"
    by (simp add: ex_unrest unrest assms closure)
  also have "... = (\<not> (\<exists> $ref \<bullet> (\<not> pre\<^sub>R (P last\<^sub>u($tr))))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
    by (rel_auto)
  also have "... = ?rhs"
    by (simp add: ex_unrest unrest assms closure usubst)
  finally show ?thesis .
qed

lemma "\<lbrakk> \<And> a. P(a) is NCSP \<rbrakk> \<Longrightarrow> (\<box> x\<in>A \<^bold>\<rightarrow> P(x)) = (\<box> x\<in>A \<^bold>\<rightarrow> Skip) ;; (P x)\<lbrakk>x\<rightarrow>last\<^sub>u($tr)\<rbrakk>"
*)

lemma st_rel_RR: "[P]\<^sub>S is RR"
  by (rel_auto)

lemma RR_msubst_tt: "RR((P t)\<lbrakk>t\<rightarrow>&tt\<rbrakk>) = (RR (P t))\<lbrakk>t\<rightarrow>&tt\<rbrakk>"
  by (rel_auto)

lemma RR_msubst_ref': "RR((P r)\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) = (RR (P r))\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>"
  by (rel_auto)
    
lemma msubst_tt_RR [closure]: "\<lbrakk> \<And> t. P t is RR \<rbrakk> \<Longrightarrow> (P t)\<lbrakk>t\<rightarrow>&tt\<rbrakk> is RR"
  by (simp add: Healthy_def RR_msubst_tt)
    
lemma msubst_ref'_RR [closure]: "\<lbrakk> \<And> r. P r is RR \<rbrakk> \<Longrightarrow> (P r)\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> is RR"
  by (simp add: Healthy_def RR_msubst_ref')  

lemma msubst_pair: "(P x y)\<lbrakk>(x, y) \<rightarrow> (e, f)\<^sub>u\<rbrakk> = (P x y)\<lbrakk>x \<rightarrow> e\<rbrakk>\<lbrakk>y \<rightarrow> f\<rbrakk>"
  by (rel_auto)

lemma CSP_mk_CRD [closure]: "[P \<turnstile> Q trace refs | R(trace)]\<^sub>C is CSP"
  by (simp add: mk_CRD_def closure unrest)

lemma preR_mk_CRD [rdes]: "pre\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = [P]\<^sub>S\<^sub><"
  by (simp add: mk_CRD_def rea_pre_RHS_design usubst unrest R2c_not R2c_lift_state_pre rea_st_cond_def, rel_auto)

lemma periR_mk_CRD [rdes]: "peri\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = ([P]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r ([Q trace refs]\<^sub>S\<^sub><)\<lbrakk>(trace,refs)\<rightarrow>(&tt,$ref\<acute>)\<^sub>u\<rbrakk>)"
  by (simp add: mk_CRD_def rea_peri_RHS_design usubst unrest R2c_not R2c_lift_state_pre
                impl_alt_def R2c_disj R2c_msubst_tt R1_disj, rel_auto)

lemma postR_mk_CRD [rdes]: "post\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = ([P]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r ([R(trace)]\<^sub>S)\<lbrakk>trace\<rightarrow>&tt\<rbrakk>)"
  by (simp add: mk_CRD_def rea_post_RHS_design usubst unrest R2c_not R2c_lift_state_pre
                impl_alt_def R2c_disj R2c_msubst_tt R1_disj, rel_auto)

text {* Refinement introduction law for contracts *}

lemma CRD_contract_refine:
  assumes
    "Q is CSP" "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R Q`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>2 t r\<rceil>\<^sub>S\<^sub><\<lbrakk>t\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk>`"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> Q"
proof -
  have "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    using assms by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, rel_auto+)
  thus ?thesis
    by (simp add: SRD_reactive_tri_design assms(1))
qed

lemma CRD_contract_refine':
  assumes
    "Q is CSP" "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R Q`"
    "\<lceil>P\<^sub>2 t r\<rceil>\<^sub>S\<^sub><\<lbrakk>t\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R Q)"
    "\<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R Q)"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> Q"
  using assms by (rule_tac CRD_contract_refine, simp_all add: refBy_order)
  
lemma CRD_refine_CRD: 
  assumes 
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> (\<lceil>Q\<^sub>1\<rceil>\<^sub>S\<^sub>< :: ('e,'s) action)`"
    "(\<lceil>P\<^sub>2 x r\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>Q\<^sub>2 x r\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> :: ('e,'s) action)"
    "\<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>Q\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> :: ('e,'s) action)"
  shows "([P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3 trace]\<^sub>C :: ('e,'s) action) \<sqsubseteq> [Q\<^sub>1 \<turnstile> Q\<^sub>2 trace refs | Q\<^sub>3 trace]\<^sub>C"
  using assms
  by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, rel_auto+)

lemma CRD_refine_rdes: 
  assumes 
    "`[P\<^sub>1]\<^sub>S\<^sub>< \<Rightarrow> Q\<^sub>1`"
    "([P\<^sub>2 x r]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>2)"
    "[P\<^sub>3 x]\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> ([P\<^sub>1]\<^sub>S\<^sub>< \<and> Q\<^sub>3)"
  shows "([P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3 trace]\<^sub>C :: ('e,'s) action) \<sqsubseteq> 
          \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  using assms
  by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, rel_auto+)
    
text {* A healthiness condition for weakly guarded CSP processes *}

definition [upred_defs]: "Productive(P) = P \<parallel>\<^sub>R \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr <\<^sub>u $tr\<acute>))"

lemma Productive_RHS_design_form:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R"
  shows "Productive(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> (R \<and> $tr <\<^sub>u $tr\<acute>))"
  using assms by (simp add: Productive_def RHS_tri_design_par unrest)

lemma Productive_form:
  "Productive(SRD(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
proof -
  have "Productive(SRD(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) \<parallel>\<^sub>R \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr <\<^sub>u $tr\<acute>))"
    by (simp add: Productive_def SRD_as_reactive_tri_design)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (simp add: RHS_tri_design_par unrest)
  finally show ?thesis .
qed

lemma Productive_post_refines_tr_increase:
  assumes "P is SRD" "P is Productive" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... = R1(R2c(pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (simp add: rea_post_RHS_design unrest usubst assms, rel_auto)
  also have "... = R1((pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (simp add: R2c_impl R2c_preR R2c_postR R2c_and R2c_tr_less_tr' assms)
  also have "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> ...)"
    by (rel_auto)
  finally show ?thesis .
qed

lemma Continuous_Productive [closure]: "Continuous Productive"
  by (simp add: Continuous_def Productive_def, rel_auto)
  
lemma Productive_Miracle [closure]:
  "Miracle is Productive"
  unfolding Miracle_tri_def Healthy_def
  by (subst Productive_RHS_design_form, simp_all add: unrest)

lemma Productive_Stop [closure]:
  "Stop is Productive"
  by (simp add: Stop_RHS_tri_design Healthy_def Productive_RHS_design_form unrest)

lemma Productive_DoCSP [closure]:
  "(do\<^sub>C a :: ('\<sigma>, '\<psi>) action) is Productive"
proof -
  have "((\<Phi>(true,id,\<langle>a\<rangle>) \<and> $tr\<acute> >\<^sub>u $tr) :: ('\<sigma>, '\<psi>) action)
        = (\<Phi>(true,id,\<langle>a\<rangle>))"
    by (rel_auto, simp add: Prefix_Order.strict_prefixI')
  hence "Productive(do\<^sub>C a) = do\<^sub>C a"
    by (simp add: Productive_RHS_design_form DoCSP_RHS_tri unrest)
  thus ?thesis
    by (simp add: Healthy_def)
qed

lemma Productive_Guard [closure]:
  assumes "P is CSP" "P is Productive" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "b &\<^sub>u P is Productive"
proof -
  have "b &\<^sub>u P = b &\<^sub>u \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... =
        \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile>
          ((pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: Guard_tri_design rea_pre_RHS_design rea_peri_RHS_design rea_post_RHS_design unrest assms
        usubst R1_preR Healthy_if R1_rea_impl R1_peri_SRD R1_extend_conj' R2c_preR R2c_not R2c_rea_impl 
        R2c_periR R2c_postR R2c_and R2c_tr_less_tr' R1_tr_less_tr')             
  also have "... = \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rel_auto)
  also have "... = Productive(b &\<^sub>u P)"
    by (simp add: Productive_def Guard_tri_design RHS_tri_design_par unrest)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma Productive_intro:
  assumes "P is SRD" "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "P is Productive"
proof -
  have P:"\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) = P"
  proof -
    have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> post\<^sub>R(P)))"
      by (metis (no_types, hide_lams) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
      by (metis assms(2) utp_pred_laws.inf.absorb1 utp_pred_laws.inf.assoc)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
      by (metis (no_types, hide_lams) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)
    finally show ?thesis
      by (simp add: SRD_reactive_tri_design assms(1))
  qed
  thus ?thesis
    by (metis Healthy_def RHS_tri_design_par Productive_def ok'_pre_unrest unrest_true utp_pred_laws.inf_right_idem utp_pred_laws.inf_top_right)
qed

lemma Productive_rdes_intro:
  assumes "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> R" "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) is Productive"
proof (rule Productive_intro)
  show "\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R) is SRD"
    by (simp add: RHS_tri_design_is_SRD assms)

  from assms(1) show "($tr\<acute> >\<^sub>u $tr) \<sqsubseteq> (pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)) \<and> post\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)))"
    apply (simp add: rea_pre_RHS_design rea_post_RHS_design usubst assms unrest)
    using assms(1) apply (rel_auto)
    apply fastforce
  done

  show "$wait\<acute> \<sharp> pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R))"
    by (simp add: rea_pre_RHS_design rea_post_RHS_design usubst R1_def R2c_def R2s_def assms unrest)
qed

lemma Productive_cond_rea [closure]:
  assumes "P is CSP" "P is Productive" "Q is CSP" "Q is Productive"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is Productive"
proof -
  have "P \<triangleleft> b \<triangleright>\<^sub>R Q =
        \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_if Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<triangleleft> b \<triangleright>\<^sub>R (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: cond_srea_form)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> (((post\<^sub>R P) \<triangleleft> b \<triangleright>\<^sub>R (post\<^sub>R Q)) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... is Productive"
    by (simp add: Healthy_def Productive_RHS_design_form  unrest)
  finally show ?thesis .
qed

lemma Productive_seq_1 [closure]:
  assumes "P is NCSP" "P is Productive" "Q is NCSP"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q)))"
    by (metis Healthy_def NCSP_implies_CSP SRD_reactive_tri_design Productive_form assms(1) assms(2) assms(3))
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>R pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q))"
    by (simp add: RHS_tri_design_composition_wp rpred unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths ex_unrest wpR_def disj_upred_def)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>R pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q)) = ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q) \<and> $tr\<acute> >\<^sub>u $tr)"
      by (rel_auto)
    thus ?thesis
      by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wpR_def)
  finally show ?thesis .
qed

lemma Productive_seq_2 [closure]:
  assumes "P is NCSP" "Q is NCSP" "Q is Productive"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P))) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_def NCSP_implies_CSP SRD_reactive_tri_design Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: RHS_tri_design_composition_wp rpred unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths ex_unrest wpR_def disj_upred_def)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "(R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr) = (R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
      by (rel_auto)
    thus ?thesis
      by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wpR_def)
  finally show ?thesis .
qed

lemma Productive_ExtChoice [closure]:
  assumes "A \<noteq> {}" "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>Productive\<rbrakk>\<^sub>H"
  shows "ExtChoice A is Productive"
proof -
  have 1: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
    using NCSP_implies_NSRD NSRD_wait'_unrest_pre assms(2) by blast
  show ?thesis
  proof (rule Productive_intro, simp_all add: assms closure rdes 1 unrest)
    have "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) =
          ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Sqinter> P\<in>A \<bullet> (pre\<^sub>R P \<and> post\<^sub>R P)))"
      by (rel_auto)
    moreover have "(\<Sqinter> P\<in>A \<bullet> (pre\<^sub>R P \<and> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> ((pre\<^sub>R P \<and> post\<^sub>R P) \<and> $tr <\<^sub>u $tr\<acute>))"
      by (rule UINF_cong, metis (no_types, lifting) "1" Ball_Collect NCSP_implies_CSP Productive_post_refines_tr_increase assms utp_pred_laws.inf.absorb1)

    ultimately show "($tr\<acute> >\<^sub>u $tr) \<sqsubseteq> ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<and> ((\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
      by (rel_auto)
  qed
qed

lemma Productive_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP" "P is Productive" "Q is Productive"
  shows "P \<box> Q is Productive"
  by (simp add: extChoice_def Productive_ExtChoice assms)

lemma Productive_PrefixCSP [closure]: "P is NCSP \<Longrightarrow> PrefixCSP a P is Productive"
  by (simp add: Healthy_if NCSP_DoCSP NCSP_implies_NSRD NSRD_is_SRD PrefixCSP_def Productive_DoCSP Productive_seq_1)

lemma Productive_InputCSP [closure]:
  "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> x?(v:A(v)) \<^bold>\<rightarrow> P(v) is Productive"
  by (auto simp add: InputCSP_def unrest closure intro: Productive_ExtChoice)

lemma preR_Productive [rdes]:
  assumes "P is CSP"
  shows "pre\<^sub>R(Productive(P)) = pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(Productive(P)) = pre\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def Productive_form assms)
  thus ?thesis
    by (simp add: rea_pre_RHS_design usubst unrest R2c_not R2c_preR R1_preR Healthy_if assms)
qed

lemma periR_Productive [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(Productive(P)) = peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(Productive(P)) = peri\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def NCSP_implies_CSP Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))"
    by (simp add: rea_peri_RHS_design usubst unrest R2c_not assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)"
    by (simp add: R1_rea_impl R2c_rea_impl R2c_preR R2c_peri_SRD
                  R1_peri_SRD assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis
    by (simp add: SRD_peri_under_pre assms unrest closure)
qed

lemma postR_Productive [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(Productive(P)) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)"
proof -
  have "post\<^sub>R(Productive(P)) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def NCSP_implies_CSP Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr))"
    by (simp add: rea_post_RHS_design usubst unrest assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)"
    by (simp add: R1_rea_impl R2c_rea_impl R2c_preR R2c_and R1_extend_conj' R2c_post_SRD
             R1_post_SRD assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis .
qed
  
lemma preR_frame_seq_export:
  assumes "P is NCSP" "P is Productive" "Q is NCSP"
  shows "(pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q) = (pre\<^sub>R P \<and> (post\<^sub>R P ;; Q))"
proof -
  have "(pre\<^sub>R P \<and> (post\<^sub>R P ;; Q)) = (pre\<^sub>R P \<and> ((pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; Q))"
    by (simp add: SRD_post_under_pre assms closure unrest)
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) ;; Q \<or> (pre\<^sub>R P \<Rightarrow>\<^sub>r R1(post\<^sub>R P)) ;; Q)))"
    by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms(1) rea_impl_def seqr_or_distl R1_preR Healthy_if)
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) ;; Q \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"
  proof -
    have "(pre\<^sub>R P \<or> \<not>\<^sub>r pre\<^sub>R P) = R1 true"
      by (simp add: R1_preR rea_not_or)
    then show ?thesis
      by (metis (no_types, lifting) R1_def R1_idem conj_comm disj_comm disj_conj_distr rea_impl_def seqr_or_distl utp_pred_laws.inf_top_left utp_pred_laws.sup.left_idem)
  qed
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"
    by (simp add: NSRD_neg_pre_left_zero assms closure SRD_healths)
  also have "... = (pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)"
    by (rel_blast)
  finally show ?thesis ..
qed

(*
lemma ExtChoice_seq_distr:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>Productive\<rbrakk>\<^sub>H" "A \<noteq> {}" "Q is NCSP"
  shows "(\<box> P\<in>A \<bullet> P) ;; Q = (\<box> P\<in>A \<bullet> P ;; Q)"
proof -
  have [closure]: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
    by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_wait'_unrest_pre assms(1))
  have [closure]: "(\<lambda>P. NCSP(P) ;; Q) ` A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (auto simp add: Healthy_if closure assms(1) assms(4))
  have nc2: "(\<box> P\<in>A \<bullet> P ;; Q) = (\<box> P\<in>A \<bullet> NCSP(P) ;; Q)"
    by (rule_tac ExtChoice_cong, simp add: Healthy_if closure assms)

  have p1: "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) wp\<^sub>R pre\<^sub>R Q =
            (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R P \<Rightarrow> post\<^sub>R P) wp\<^sub>R pre\<^sub>R Q)"
      by (simp add: UINF_impl[THEN sym] wp)
    also have "... = (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)"
      by (rule USUP_cong, simp add: SRD_post_under_pre closure assms Healthy_if)
    finally show ?thesis .
  qed

  have p2: "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)"
  proof -
    have "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R P \<Rightarrow> post\<^sub>R P)"
      by (rel_auto)
    also have "... = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)"
      by (rule UINF_cong, simp add:  SRD_post_under_pre assms(1) closure)
    finally show ?thesis .
  qed

  -- {* We perform the proof by showing the pre-, peri- and postconditions are the same *}

  have pre: "pre\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = pre\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)"
  proof -
    have "pre\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) wp\<^sub>R pre\<^sub>R Q)"
      by (simp add: rdes closure assms wp)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q))"
      by (simp add: p1)
    also have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R P \<and> (post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)))"
      by (rel_blast)
    also have "... = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P) \<and> post\<^sub>R (NCSP P) wp\<^sub>R pre\<^sub>R Q)"
      by (rule USUP_cong, simp add: closure assms Healthy_if)
    also have "... = pre\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)"
      by (simp add: rdes closure assms nc2)
    finally show ?thesis .
  qed

  have peri: "peri\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = peri\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)" (is "?lhs = ?rhs")
    apply (simp_all add: rdes nc2 closure assms p1 spec_cond_dist)
  proof -
    have "?rhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  (\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q \<Rightarrow> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                   (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q \<Rightarrow> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
        apply (simp_all add: rdes nc2 closure assms p1 spec_cond_dist unrest)
        apply (subst USUP_healthy[of "A" "NCSP", THEN sym], simp add: assms)+
        apply (subst UINF_healthy[of "A" "NCSP", THEN sym], simp add: assms)+
        apply (simp)
    done
    also
    have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                   (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (rel_blast)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (simp add: spec_cond_dist[THEN sym] UINF_conj_UINF)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> pre\<^sub>R P \<and> (post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (rel_auto)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> pre\<^sub>R P \<and> ((post\<^sub>R P \<and> $tr <\<^sub>u $tr\<acute>) ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      oops
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
                  ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P) ;; peri\<^sub>R Q))"
      apply (rel_simp, safe)
      apply blast+
      apply meson+



    have "?lhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
                  ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P) ;; peri\<^sub>R Q))"
      by (simp_all add: rdes nc2 closure assms p1 spec_cond_dist, simp add: p2, rel_auto)
    (*
"     ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
     ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
     ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) ;; peri\<^sub>R Q)" *)


    apply (subst rdes)
    apply (simp_all add: closure assms)
*)

lemma PrefixCSP_dist:
  "PrefixCSP a (P \<sqinter> Q) = (PrefixCSP a P) \<sqinter> (PrefixCSP a Q)"
  using Continuous_Disjunctous Disjunctuous_def PrefixCSP_Continuous by auto

lemma DoCSP_is_Prefix:
  "do\<^sub>C(a) = PrefixCSP a Skip"
  by (simp add: PrefixCSP_def Healthy_if closure, metis CSP4_DoCSP CSP4_def Healthy_def)

lemma Prefix_CSP_seq:
  assumes "P is CSP" "Q is CSP"
  shows "(PrefixCSP a P) ;; Q = (PrefixCSP a (P ;; Q))"
  by (simp add: PrefixCSP_def seqr_assoc Healthy_if assms closure)

subsection {* Guarded recursion *}

text {* Proofs that guarded recursion yields a unique fixed-point *}

text {* Guardedness variant *}

definition gvrt :: "(('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) chain" where
[upred_defs]: "gvrt(n) \<equiv> ($tr \<le>\<^sub>u $tr\<acute> \<and> #\<^sub>u(&tt) <\<^sub>u \<guillemotleft>n\<guillemotright>)"

lemma gvrt_chain: "chain gvrt"
  apply (simp add: chain_def, safe)
  apply (rel_simp)
  apply (rel_simp)+
done

lemma gvrt_limit: "\<Sqinter> (range gvrt) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto)

definition Guarded :: "(('\<sigma>,'\<phi>) action \<Rightarrow> ('\<sigma>,'\<phi>) action) \<Rightarrow> bool" where
"Guarded(F) = (\<forall> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)))"

lemma GuardedI: "\<lbrakk> \<And> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)) \<rbrakk> \<Longrightarrow> Guarded F"
  by (simp add: Guarded_def)

theorem guarded_fp_uniq:
  assumes "mono F" "F \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H" "Guarded F"
  shows "\<mu> F = \<nu> F"
proof -
  have "constr F gvrt"
    using assms    
    by (auto simp add: constr_def gvrt_chain Guarded_def tcontr_alt_def')
  hence "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = ($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F)"
    apply (rule constr_fp_uniq)
    apply (simp add: assms)
    using gvrt_limit apply blast
  done
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = \<mu> F"
  proof -
    have "\<mu> F is R1"
      by (rule SRD_healths(1), rule Healthy_mu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F) = \<nu> F"
  proof -
    have "\<nu> F is R1"
      by (rule SRD_healths(1), rule Healthy_nu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  ultimately show ?thesis
    by (simp)
qed

lemma Guarded_const [closure]: "Guarded (\<lambda> X. P)"
  by (simp add: Guarded_def)

lemma Guarded_if_Productive [closure]:
  fixes P :: "('\<sigma>,'\<phi>) action"
  assumes "P is NSRD" "P is Productive"
  shows "Guarded (\<lambda> X. P ;; CSP(X))"
proof (clarsimp simp add: Guarded_def)
  -- {* We split the proof into three cases corresponding to valuations for ok, wait, and wait'
        respectively. *}
  fix X n
  have a:"(P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk> =
        (P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_1 assms)
  have b:"((P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> =
          ((P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_2 assms)
  have c:"((P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk> =
          ((P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk>"
  proof -
    have 1:"(P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          (P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      by (metis (no_types, lifting) Healthy_def R3h_wait_true SRD_healths(3) SRD_idem)
    have 2:"(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
    proof -
      have exp:"\<And> Y::('\<sigma>,'\<phi>) action. (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                  ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>))
                     \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      proof -
        fix Y :: "('\<sigma>,'\<phi>) action"

        have "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
              ((\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (metis (no_types) Healthy_def Productive_form assms(1) assms(2) NSRD_is_SRD)
        also have "... =
             ((R1(R2c(pre\<^sub>R(P) \<Rightarrow> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def RD1_def RD2_def usubst unrest assms closure design_def)
        also have "... =
             (((\<not>\<^sub>r pre\<^sub>R(P) \<or> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: impl_alt_def R2c_disj R1_disj R2c_not  assms closure R2c_and
              R2c_preR rea_not_def R1_extend_conj' R2c_ok' R2c_post_SRD R1_tr_less_tr' R2c_tr_less_tr')
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> ($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: usubst unrest assms closure seqr_or_distl NSRD_neg_pre_left_zero SRD_healths)
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        proof -
          have "($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> =
                ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<and> $ok\<acute> =\<^sub>u true) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>"
            by (rel_blast)
          also have "... = (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>\<lbrakk>true/$ok\<rbrakk>"
            using seqr_left_one_point[of ok "(post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)" True "(CSP Y)\<lbrakk>false/$wait\<rbrakk>"]
            by (simp add: true_alt_def[THEN sym])
          finally show ?thesis by (simp add: usubst unrest)
        qed
        finally
        show "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                 ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>))
                 \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>" .
      qed

      have 1:"((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP X)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n)) =
              ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP (X \<and> gvrt n))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n))"
          apply (rel_auto)
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok')
          apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="ref\<^sub>0" in exI)
          apply (simp)
          apply (erule Prefix_Order.strict_prefixE')
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok' z zs)
          apply (simp add: length_minus_list)
          apply (subgoal_tac "length(tr) + length(z # zs) \<le> length(tr')")
          apply auto[1]
          apply (metis diff_add_cancel_left' length_append nat_le_iff_add plus_list_def)
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok')
          apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="ref\<^sub>0" in exI)
          apply (simp)
          apply (erule Prefix_Order.strict_prefixE')
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok' z zs)
          apply (simp add: length_minus_list)
          apply (subgoal_tac "length(tr) + length(z # zs) \<le> length(tr')")
          apply auto[1]
          apply (metis Prefix_Order.prefix_length_le length_append)
        done
        have 2:"(\<not>\<^sub>r pre\<^sub>R P) ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> = (\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>"
          by (simp add: NSRD_neg_pre_left_zero closure assms SRD_healths)
        show ?thesis
          by (simp add: exp 1 2 utp_pred_laws.inf_sup_distrib2)
      qed

      show ?thesis
      proof -
      have "(P ;; (CSP X) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
      by (subst seqr_bool_split[of wait], simp_all add: usubst utp_pred_laws.distrib(4))
      also
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
                 (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
        by (simp add: 1 2)
      also
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<or>
                    P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (simp add: usubst utp_pred_laws.distrib(4))
      also have "... = (P ;; (CSP (X \<and> gvrt n)) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (subst seqr_bool_split[of wait], simp_all add: usubst)
      finally show ?thesis by (simp add: usubst)
    qed

  qed
  show "(P ;; CSP(X) \<and> gvrt (Suc n)) = (P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))"
    apply (rule_tac bool_eq_splitI[of "in_var ok"])
    apply (simp_all add: a)
    apply (rule_tac bool_eq_splitI[of "in_var wait"])
    apply (simp_all add: b c)
  done
qed

lemma PrefixCSP_Guarded [closure]: "Guarded (PrefixCSP a)"
proof -
  have "PrefixCSP a = (\<lambda> X. do\<^sub>C(a) ;; CSP(X))"
    by (simp add: fun_eq_iff PrefixCSP_def)
  thus ?thesis
    using Guarded_if_Productive NCSP_DoCSP NCSP_implies_NSRD Productive_DoCSP by auto
qed

lemma ExtChoice_Guarded [closure]:
  assumes  "\<And> P. P \<in> A \<Longrightarrow> Guarded P"
  shows "Guarded (\<lambda> X. \<box>P\<in>A \<bullet> P(X))"
proof (rule GuardedI)
  fix X n
  have "\<And> Y. ((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    fix Y
    let ?lhs = "((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1))" and ?rhs = "((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
    have a:"?lhs\<lbrakk>false/$ok\<rbrakk> = ?rhs\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto)
    have b:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk>"
      by (rel_auto)
    have c:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk>"
      by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest, rel_blast)
    show "?lhs = ?rhs"
      using a b c
      by (rule_tac bool_eq_splitI[of "in_var ok"], simp, rule_tac bool_eq_splitI[of "in_var wait"], simp_all)
  qed
  moreover have "((\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) \<and> gvrt(n+1)) =  ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    have "(\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) = (\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1)))"
    proof (rule ExtChoice_cong)
      fix P assume "P \<in> A"
      thus "(P X \<and> gvrt(n+1)) = (P (X \<and> gvrt(n)) \<and> gvrt(n+1))"
        using Guarded_def assms by blast
    qed
    thus ?thesis by simp
  qed
  ultimately show "((\<box>P\<in>A \<bullet> P X) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)))) \<and> gvrt(n+1))"
    by simp
qed

lemma extChoice_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<box> Q(X))"
proof -
  have "Guarded (\<lambda> X. \<box>F\<in>{P,Q} \<bullet> F(X))"
    by (rule ExtChoice_Guarded, auto simp add: assms)
  thus ?thesis
    by (simp add: extChoice_def)
qed

lemma Continuous_mu_CSP_form_1 [closure]: "Continuous (\<lambda>X. P ;; CSP X)"
  using SRD_Continuous
  by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], rename_tac A, drule_tac x="A" in spec, simp)

lemma mu_CSP_form_1_type [closure]:
  assumes "P is CSP"
  shows "(\<lambda>X. P ;; CSP X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  by (blast intro: funcsetI closure assms)

text {* Example fixed-point calculation *}

lemma mu_csp_form_1 [rdes]:
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; CSP(X)) = (\<Sqinter>i \<bullet> P \<^bold>^ (i+1)) ;; Miracle"
proof -
  have 1:"Continuous (\<lambda>X. P ;; CSP X)"
    using SRD_Continuous
    by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], drule_tac x="A" in spec, simp)
  have 2: "(\<lambda>X. P ;; CSP X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (blast intro: funcsetI closure assms)
  with 1 2 have "(\<mu> X \<bullet> P ;; CSP(X)) = (\<nu> X \<bullet> P ;; CSP(X))"
    by (simp add: guarded_fp_uniq Guarded_if_Productive[OF assms] Continuous_Monotonic funcsetI closure)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ i) false)"
    by (simp add: sup_continuous_lfp 1 sup_continuous_Continuous false_upred_def)
  also have "... = ((\<lambda>X. P ;; CSP X) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1) ;; Miracle)"
  proof (rule SUP_cong,simp_all)
    fix i
    show "P ;; CSP (((\<lambda>X. P ;; CSP X) ^^ i) false) = (P ;; P \<^bold>^ i) ;; Miracle"
    proof (induct i)
      case 0
      then show ?case
        by (simp, metis srdes_hcond_def srdes_theory_continuous.healthy_top)
    next
      case (Suc i)
      then show ?case
        by (simp add: Healthy_if NSRD_is_SRD SRD_power_Suc SRD_seqr_closure assms(1) seqr_assoc srdes_theory_continuous.weak.top_closed)
    qed
  qed
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1)) ;; Miracle"
    by (simp add: seq_Sup_distr)
  finally show ?thesis
    by (simp add: UINF_as_Sup[THEN sym])
qed

lemma mu_csp_form_NSRD [closure]:
  assumes "P is NCSP" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; CSP(X)) is NSRD"
  by (simp add: mu_csp_form_1 assms closure)

lemma mu_csp_form_1':
  assumes "P is NCSP" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; CSP(X)) = (P ;; P\<^sup>\<star>) ;; Miracle"
proof -
  have "(\<mu> X \<bullet> P ;; CSP(X)) = (\<Sqinter> i\<in>UNIV \<bullet> P ;; P \<^bold>^ i) ;; Miracle"
    by (simp add: mu_csp_form_1 assms closure ustar_def)
  also have "... = (P ;; P\<^sup>\<star>) ;; Miracle"
    by (simp only: seq_UINF_distl[THEN sym], simp add: ustar_def)
  finally show ?thesis .
qed

lemma mu_example1: "(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = (\<Sqinter>i \<bullet> do\<^sub>C(\<guillemotleft>a\<guillemotright>) \<^bold>^ (i+1)) ;; Miracle"
  by (simp add: PrefixCSP_def mu_csp_form_1 closure)
    
lemma preR_mu_example1 [rdes]: "pre\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = true\<^sub>r"
  by (simp add: mu_example1 rdes closure unrest wp)

lemma UINF_ind_R1_closed [closure]:
  "\<lbrakk> \<And> i. P(i) is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<bullet> P(i)) is R1"
  by (rel_blast)

lemma UINF_R1_closed [closure]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<in> A \<bullet> P i) is R1"
  by (rel_blast)
    
lemma tr_ext_conj_R1 [closure]: 
  "$tr\<acute> =\<^sub>u $tr ^\<^sub>u e \<and> P is R1"
  by (rel_auto, simp add: Prefix_Order.prefixI)

lemma tr_id_conj_R1 [closure]: 
  "$tr\<acute> =\<^sub>u $tr \<and> P is R1"
  by (rel_auto)
    
lemma periR_mu_example1 [rdes]:
  "peri\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = (\<Sqinter> i \<bullet> \<Phi>(true, id, \<langle>\<guillemotleft>a\<guillemotright>\<rangle>) \<^bold>^ i ;; \<E>(true, \<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u))"
  by (simp add: mu_example1 rdes rpred closure unrest wp seq_UINF_distr alpha)

lemma postR_mu_example1 [rdes]:
  "post\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = false"
  by (simp add: mu_example1 rdes closure unrest wp)

lemma SRD_refine_intro':
  assumes
    "P is SRD" "Q is SRD"
    "`pre\<^sub>R(P) \<Rightarrow> pre\<^sub>R(Q)`" "peri\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> peri\<^sub>R(Q))" "post\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(Q))"
  shows "P \<sqsubseteq> Q"
  using assms by (rule_tac SRD_refine_intro, simp_all add: refBy_order)
        
lemma mu_csp_expand [rdes]: "(\<mu>\<^sub>C (op ;; Q)) = (\<mu> X \<bullet> Q ;; CSP X)"
  by (simp add: comp_def)
    
lemma mu_csp_basic_refine:
  assumes 
    "P is CSP" "Q is NCSP" "Q is Productive" "pre\<^sub>R(P) = true\<^sub>r" "pre\<^sub>R(Q) = true\<^sub>r"
    "peri\<^sub>R P \<sqsubseteq> peri\<^sub>R Q"
    "peri\<^sub>R P \<sqsubseteq> post\<^sub>R Q ;; peri\<^sub>R P"
  shows "P \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> Q ;; X)"
proof (rule SRD_refine_intro', simp_all add: closure usubst alpha rpred rdes unrest wp seq_UINF_distr assms)
  show "peri\<^sub>R P \<sqsubseteq> (\<Sqinter> i \<bullet> post\<^sub>R Q \<^bold>^ i ;; peri\<^sub>R Q)"
  proof (rule UINF_refines')
    fix i
    show "peri\<^sub>R P \<sqsubseteq> post\<^sub>R Q \<^bold>^ i ;; peri\<^sub>R Q"
    proof (induct i)
      case 0
      then show ?case by (simp add: assms)
    next
      case (Suc i)
      then show ?case
        by (meson assms(6) assms(7) semilattice_sup_class.le_sup_iff upower_inductl)
    qed
  qed
qed
  
lemma CRD_mu_basic_refine:
  fixes P :: "'e list \<Rightarrow> 'e set \<Rightarrow> 's upred"
  assumes
    "Q is NCSP" "Q is Productive" "pre\<^sub>R(Q) = true\<^sub>r"
    "[P t r]\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(&tt, $ref\<acute>)\<^sub>u\<rbrakk> \<sqsubseteq> peri\<^sub>R Q"
    "[P t r]\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(&tt, $ref\<acute>)\<^sub>u\<rbrakk> \<sqsubseteq> post\<^sub>R Q ;;\<^sub>h [P t r]\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(&tt, $ref\<acute>)\<^sub>u\<rbrakk>"
  shows "[true \<turnstile> P trace refs | R]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> Q ;; X)"
proof (rule mu_csp_basic_refine, simp_all add: msubst_pair assms closure alpha rdes rpred Healthy_if R1_false)
  show "[P trace refs]\<^sub>S\<^sub><\<lbrakk>trace\<rightarrow>&tt\<rbrakk>\<lbrakk>refs\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq> peri\<^sub>R Q"
    using assms by (simp add: msubst_pair)
  show "[P trace refs]\<^sub>S\<^sub><\<lbrakk>trace\<rightarrow>&tt\<rbrakk>\<lbrakk>refs\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq> post\<^sub>R Q ;; [P trace refs]\<^sub>S\<^sub><\<lbrakk>trace\<rightarrow>&tt\<rbrakk>\<lbrakk>refs\<rightarrow>$ref\<acute>\<rbrakk>"
    using assms by (simp add: msubst_pair)
qed

subsection {* Merge predicates *}

definition CSPInnerMerge :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("N\<^sub>C") where
  [upred_defs]:
  "CSPInnerMerge ns1 cs ns2 = (
    $ref\<acute> \<subseteq>\<^sub>u (($0-ref \<union>\<^sub>u $1-ref) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u (($0-ref \<inter>\<^sub>u $1-ref) - \<guillemotleft>cs\<guillemotright>) \<and>
    $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
    ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> ($1-tr - $tr\<^sub><) \<and>
    ($0-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u ($1-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and>
    $st\<acute> =\<^sub>u ($st\<^sub>< \<oplus> $0-st on &ns1) \<oplus> $1-st on &ns2)"

text {* An intermediate merge hides the state, whilst a final merge hides the refusals. *}
  
definition CSPInterMerge ("_ \<lbrakk>_|_|_\<rbrakk>\<^sup>I _" [85,0,0,0,86] 86) where
[upred_defs]: "(P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q) = (P \<parallel>\<^bsub>(\<exists> $st\<acute> \<bullet> N\<^sub>C ns1 cs ns2)\<^esub> Q)"
  
definition CSPFinalMerge ("_ \<lbrakk>_|_|_\<rbrakk>\<^sup>F _" [85,0,0,0,86] 86) where
[upred_defs]: "(P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q) = (P \<parallel>\<^bsub>(\<exists> $ref\<acute> \<bullet> N\<^sub>C ns1 cs ns2)\<^esub> Q)"
  
abbreviation wrC ("_ wr[_|_|_]\<^sub>C _" [85,0,0,0,86] 86) where
"P wr[ns1|cs|ns2]\<^sub>C Q \<equiv> P wr\<^sub>R(N\<^sub>C ns1 cs ns2) Q"

lemma CSPInnerMerge_R2m [closure]: "N\<^sub>C ns1 cs ns2 is R2m"
  by (rel_auto)

lemma CSPInnerMerge_RDM [closure]: "N\<^sub>C ns1 cs ns2 is RDM"
  by (rule RDM_intro, simp add: closure, simp_all add: CSPInnerMerge_def unrest)

lemma ex_ref'_R2m_closed [closure]: 
  assumes "P is R2m"
  shows "(\<exists> $ref\<acute> \<bullet> P) is R2m"
proof -
  have "R2m(\<exists> $ref\<acute> \<bullet> R2m P) = (\<exists> $ref\<acute> \<bullet> R2m P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms) 
qed
  
lemma CSPInnerMerge_unrests [unrest]: 
  "$ok\<^sub>< \<sharp> N\<^sub>C ns1 cs ns2"
  "$wait\<^sub>< \<sharp> N\<^sub>C ns1 cs ns2"
  by (rel_auto)+
    
lemma CSPInterMerge_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q is RR"
  by (simp add: CSPInterMerge_def parallel_RR_closed assms closure unrest)

lemma CSPInterMerge_unrest_st' [unrest]:
  "$st\<acute> \<sharp> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q"
  by (rel_auto)
    
lemma CSPFinalMerge_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q is RR"
  by (simp add: CSPFinalMerge_def parallel_RR_closed assms closure unrest)
    
definition CSPMerge :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("M\<^sub>C") where
[upred_defs]: "M\<^sub>C ns1 cs ns2 = M\<^sub>R(N\<^sub>C ns1 cs ns2) ;; Skip"
  
lemma swap_CSPInnerMerge:
  "ns1 \<bowtie> ns2 \<Longrightarrow> swap\<^sub>m ;; (N\<^sub>C ns1 cs ns2) = (N\<^sub>C ns2 cs ns1)"
  apply (rel_auto)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
done
    
lemma SymMerge_CSPInnerMerge_NS [closure]: "N\<^sub>C 0\<^sub>L cs 0\<^sub>L is SymMerge"
  by (simp add: Healthy_def swap_CSPInnerMerge)
                             
lemma CSPInterMerge_false [rpred]: "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I false = false"
  by (simp add: CSPInterMerge_def)

lemma CSPFinalMerge_false [rpred]: "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F false = false"
  by (simp add: CSPFinalMerge_def)
    
lemma CSPInterMerge_commute:
  assumes "ns1 \<bowtie> ns2"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>I P"
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q = P \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> N\<^sub>C ns1 cs ns2\<^esub> Q"
    by (simp add: CSPInterMerge_def)
  also have "... = P \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> (swap\<^sub>m ;; N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = P \<parallel>\<^bsub>swap\<^sub>m ;; (\<exists> $st\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: seqr_exists_right)
  also have "... = Q \<parallel>\<^bsub>(\<exists> $st\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> P"
    by (simp add: par_by_merge_commute_swap[THEN sym])
  also have "... = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>I P"
    by (simp add: CSPInterMerge_def)
  finally show ?thesis .
qed

lemma CSPFinalMerge_commute:
  assumes "ns1 \<bowtie> ns2"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = P \<parallel>\<^bsub>\<exists> $ref\<acute> \<bullet> N\<^sub>C ns1 cs ns2\<^esub> Q"
    by (simp add: CSPFinalMerge_def)
  also have "... = P \<parallel>\<^bsub>\<exists> $ref\<acute> \<bullet> (swap\<^sub>m ;; N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = P \<parallel>\<^bsub>swap\<^sub>m ;; (\<exists> $ref\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: seqr_exists_right)
  also have "... = Q \<parallel>\<^bsub>(\<exists> $ref\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> P"
    by (simp add: par_by_merge_commute_swap[THEN sym])
  also have "... = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
    by (simp add: CSPFinalMerge_def)
  finally show ?thesis .
qed
  
text {* Important theorem that shows the form of a parallel process *}

lemma CSPInnerMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" 
  shows
  "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have P:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(P)) = P" (is "?P' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms RR_implies_R2 unrest closure)
  have Q:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(Q)) = Q" (is "?Q' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms RR_implies_R2 unrest closure)
  from assms(1,2)
  have "?P' \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> ?Q' = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             ?P'\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> ?Q'\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    apply (simp add: par_by_merge_alt_def, rel_auto, blast)
    apply (rename_tac ok wait tr st ref tr' ref' ref\<^sub>0 ref\<^sub>1 st\<^sub>0 st\<^sub>1 tr\<^sub>0 ok\<^sub>0 tr\<^sub>1 wait\<^sub>0 ok\<^sub>1 wait\<^sub>1)
    apply (rule_tac x="ok" in exI)
    apply (rule_tac x="wait" in exI)
    apply (rule_tac x="tr" in exI)      
    apply (rule_tac x="st" in exI)
    apply (rule_tac x="ref" in exI)
    apply (rule_tac x="tr @ tr\<^sub>0" in exI)      
    apply (rule_tac x="st\<^sub>0" in exI)
    apply (rule_tac x="ref\<^sub>0" in exI)      
    apply (auto)
    apply (metis Prefix_Order.prefixI append_minus)
  done      
  thus ?thesis
    by (simp add: P Q)
qed

lemma CSPInterMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" 
  shows
  "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<exists> $st\<acute> \<bullet> P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q)"
    by (simp add: CSPInterMerge_def par_by_merge_def seqr_exists_right)
  also have "... = 
      (\<exists> $st\<acute> \<bullet>
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2))"
    by (simp add: CSPInnerMerge_form assms)
  also have "... = ?rhs"
    by (rel_blast)
  finally show ?thesis .
qed
  
lemma CSPFinalMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" "$ref\<acute> \<sharp> P" "$ref\<acute> \<sharp> Q"
  shows
  "(P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q) = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")  
proof -
  have "?lhs = (\<exists> $ref\<acute> \<bullet> P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q)"
    by (simp add: CSPFinalMerge_def par_by_merge_def seqr_exists_right)
  also have "... = 
      (\<exists> $ref\<acute> \<bullet>
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2))"
    by (simp add: CSPInnerMerge_form assms)
  also have "... = 
      (\<exists> $ref\<acute> \<bullet>
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             (\<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> (\<exists> $ref\<acute> \<bullet> Q)\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2))"
    by (simp add: ex_unrest assms)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             (\<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> (\<exists> $ref\<acute> \<bullet> Q)\<lbrakk>\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (rel_blast)
  also have "... = ?rhs"
    by (simp add: ex_unrest assms)
  finally show ?thesis .
qed

lemma merge_csp_do_left:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "\<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> P = 
     (\<^bold>\<exists> (ref\<^sub>1, st\<^sub>1, tt\<^sub>1) \<bullet> 
        [s\<^sub>0]\<^sub>S\<^sub>< \<and>
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
        $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
        $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
     (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<and>
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
        $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        $tr \<le>\<^sub>u $tr\<acute> \<and>
        &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPInnerMerge_form assms closure)
  also have "... =
     (\<^bold>\<exists> (ref\<^sub>1, st\<^sub>1, tt\<^sub>1) \<bullet> 
        [s\<^sub>0]\<^sub>S\<^sub>< \<and>
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
        $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
        $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (rel_blast)
  finally show ?thesis .
qed

lemma merge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) = 
     (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
        [s\<^sub>1]\<^sub>S\<^sub>< \<and>
        $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
        $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2 )"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
    (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and>
             &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPInnerMerge_form assms closure)
  also have "... = ?rhs"
    by (rel_blast)
  finally show ?thesis .
qed 
  
text {* The result of merge two terminated stateful traces is to (1) require both state preconditions
  hold, (2) merge the traces using, and (3) merge the state using a parallel assignment. *}

lemma FinalMerge_csp_do_left:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR" "$ref\<acute> \<sharp> P"
  shows "\<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F P =         
         (\<^bold>\<exists> (st\<^sub>1, t\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> P \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>t\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>t\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(\<exists> $ref\<acute> \<bullet> P) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPFinalMerge_form ex_unrest Healthy_if unrest closure assms)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>1, tt\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(\<exists> $ref\<acute> \<bullet> P) \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (rel_blast)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>1, t\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> P \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>t\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>t\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: ex_unrest Healthy_if unrest closure assms)
  finally show ?thesis .
qed
      
lemma FinalMerge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR" "$ref\<acute> \<sharp> P"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) =         
         (\<^bold>\<exists> (st\<^sub>0, t\<^sub>0) \<bullet> 
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> P \<and>
             [s\<^sub>1]\<^sub>S\<^sub>< \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) = \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
    by (simp add: assms CSPFinalMerge_commute)
  also have "... = ?rhs"
    apply (simp add: FinalMerge_csp_do_left assms lens_indep_sym conj_comm)
    apply (rel_auto)
    using assms(3) lens_indep.lens_put_comm tr_par_sym apply fastforce+
  done
  finally show ?thesis .
qed
  
lemma FinalMerge_csp_do [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
         ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> [\<langle>\<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2\<rangle>\<^sub>a]\<^sub>S)" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPFinalMerge_form unrest closure assms)
  also have "... = 
        ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> [\<langle>\<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2\<rangle>\<^sub>a]\<^sub>S)"
    by (rel_auto)
  finally show ?thesis .
qed
  
lemma InterMerge_csp_enable [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
          ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and>
           (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 \<inter>\<^sub>u E\<^sub>2 \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((E\<^sub>1 \<union>\<^sub>u E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
           [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
    by (simp add: CSPInterMerge_form unrest closure assms)
  also have "... = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
    by (rel_auto)
  also have "... = 
        ( [s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and>
          (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 \<inter>\<^sub>u E\<^sub>2 \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((E\<^sub>1 \<union>\<^sub>u E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
          [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t
         )"  
    apply (rel_auto)
    apply (rename_tac tr st tr' ref')
    apply (rule_tac x="- \<lbrakk>E\<^sub>1\<rbrakk>\<^sub>e st" in exI)
    apply (simp)
    apply (rule_tac x="- \<lbrakk>E\<^sub>2\<rbrakk>\<^sub>e st" in exI)
    apply (auto)
  done
  finally show ?thesis .
qed

lemma InterMerge_csp_enable_csp_do [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
           ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
           [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
    by (simp add: CSPInterMerge_form unrest closure assms)
  also have "... = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, tt\<^sub>0) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [s\<^sub>2]\<^sub>S\<^sub>< \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)"
    by (rel_auto) 
  also have "... = ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
                    [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)"
    by (rel_auto) 
  finally show ?thesis .
qed

lemma InterMerge_csp_do_csp_enable [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
           ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>2 - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
           [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)" 
  (is "?lhs = ?rhs")
proof -
  have "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>I \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1)"
    by (simp add: CSPInterMerge_commute assms)
  also have "... = ?rhs"
    by (simp add: InterMerge_csp_enable_csp_do assms lens_indep_sym trace_merge_commute conj_comm eq_upred_sym)
  finally show ?thesis .
qed
  
lemma par_by_merge_seq_remove: "(P \<parallel>\<^bsub>M ;; R\<^esub> Q) = (P \<parallel>\<^bsub>M\<^esub> Q) ;; R"
  by (simp add: par_by_merge_seq_add[THEN sym])
  
lemma merge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RC"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) wr[ns1|cs|ns2]\<^sub>C P = undefined"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
              [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r RC(P)) \<and>
              [s\<^sub>1]\<^sub>S\<^sub>< \<and>
              $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
              [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
              $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2) ;; R1 true)"
    by (simp add: wrR_def par_by_merge_seq_remove merge_csp_do_right closure assms Healthy_if rpred)
 also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
              [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r RC(P)) \<and>
              [s\<^sub>1]\<^sub>S\<^sub>< \<and>
              $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
              [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t ;; true\<^sub>r \<and> 
              $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2))"
   apply (rel_auto)


oops

  
subsection {* Parallel Operator *}

abbreviation ParCSP ::
  "('\<sigma>, '\<theta>) action \<Rightarrow> ('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<theta> event set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" ("_ \<lbrakk>_\<parallel>_\<parallel>_\<rbrakk> _" [75,0,0,0,76] 76) where
"P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q \<equiv> P \<parallel>\<^bsub>M\<^sub>C ns1 cs ns2\<^esub> Q"

abbreviation ParCSP_NS ::
  "('\<sigma>, '\<theta>) action \<Rightarrow> '\<theta> event set \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" (infixr "\<lbrakk>_\<rbrakk>\<^sub>C" 75) where
"P \<lbrakk>cs\<rbrakk>\<^sub>C Q \<equiv> P \<lbrakk>0\<^sub>L\<parallel>cs\<parallel>0\<^sub>L\<rbrakk> Q"

abbreviation InterleaveCSP ::
  "('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" (infixr "|||" 75) where
"P ||| Q \<equiv> P \<lbrakk>0\<^sub>L\<parallel>{}\<parallel>0\<^sub>L\<rbrakk> Q"

definition CSP5 :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "CSP5(P) = (P ||| Skip)"

definition C2 :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "C2(P) = (P \<lbrakk>1\<^sub>L\<parallel>{}\<parallel>0\<^sub>L\<rbrakk> Skip)"

lemma Skip_right_form:
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "$st\<acute> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) ;; Skip = \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> (\<exists> $ref\<acute> \<bullet> P\<^sub>3))"
proof -
  have 1:"RR(P\<^sub>3) ;; \<Phi>(true,id,\<langle>\<rangle>) = (\<exists> $ref\<acute> \<bullet> RR(P\<^sub>3))"
    by (rel_auto)
  show ?thesis
    by (rdes_simp cls: assms, metis "1" Healthy_if assms(3))
qed
  
lemma ParCSP_rdes_def [rdes_def]:
  fixes P\<^sub>1 :: "('s,'e) action"
  assumes "P\<^sub>1 is CRC" "Q\<^sub>1 is CRC" "P\<^sub>2 is CRR" "Q\<^sub>2 is CRR" "P\<^sub>3 is CRR" "Q\<^sub>3 is CRR" 
          "$st\<acute> \<sharp> P\<^sub>2" "$st\<acute> \<sharp> Q\<^sub>2" 
          "ns1 \<bowtie> ns2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = 
         \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
              (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
             ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
             ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)))"
  (is "?P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> ?Q = ?rhs")
proof -
  have "?P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> ?Q = (?P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> ?Q) ;;\<^sub>h Skip"
    by (simp add: CSPMerge_def par_by_merge_seq_add)
  also 
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) ;;\<^sub>h Skip"
    by (simp add: parallel_rdes_def swap_CSPInnerMerge CSPInterMerge_def closure assms)
  also 
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
                    (\<exists> $ref\<acute> \<bullet> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3))))"
     by (simp add: Skip_right_form  closure parallel_RR_closed assms unrest)
  also
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)))"
  proof -
    have "(\<exists> $ref\<acute> \<bullet> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3))) = ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3))"
      by (rel_blast)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed
       
subsubsection {* CSP Parallel Laws *}

lemma ParCSP_expand:
  "P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q = (P \<parallel>\<^sub>R\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q) ;; Skip"
  by (simp add: CSPMerge_def par_by_merge_seq_add)
    
lemma parallel_is_CSP [closure]:
  assumes "P is CSP" "Q is CSP"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is CSP"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) ;; Skip is CSP"
    by (simp add: closure)
  thus ?thesis
    by (simp add: CSPMerge_def par_by_merge_seq_add)
qed  
      
lemma parallel_is_CSP3 [closure]:
  assumes "P is CSP" "P is CSP3" "Q is CSP" "Q is CSP3"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is CSP3"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) ;; Skip is CSP"
    by (simp add: closure)
  thus ?thesis
    oops

theorem parallel_commutative:
  assumes "ns1 \<bowtie> ns2"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = (Q \<lbrakk>ns2\<parallel>cs\<parallel>ns1\<rbrakk> P)"
proof -
  have "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = P \<parallel>\<^bsub>swap\<^sub>m ;; (M\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: CSPMerge_def seqr_assoc swap_merge_rd swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = Q \<lbrakk>ns2\<parallel>cs\<parallel>ns1\<rbrakk> P"
    by (metis par_by_merge_commute_swap)
  finally show ?thesis .
qed

lemma interleave_commute:
  "P ||| Q = Q ||| P"
  using parallel_commutative zero_lens_indep by blast

text {* The form of C2 tells us that a normal CSP process has a downward closed set of refusals *}
  
lemma C2_form:
  assumes "P is NCSP"
  shows "C2(P) = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
proof -
  have 1:"\<Phi>(true,id,\<langle>\<rangle>) wr[1\<^sub>L|{}|0\<^sub>L]\<^sub>C pre\<^sub>R P = pre\<^sub>R P" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
                   [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<exists> $ref\<acute>;$st\<acute> \<bullet> RR(\<not>\<^sub>r pre\<^sub>R P)) \<and>
                    $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright> \<and> [\<guillemotleft>trace\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>]\<^sub>t \<and> 
                    $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &\<Sigma> \<oplus> \<guillemotleft>id\<guillemotright>($st)\<^sub>a on &\<emptyset>) ;; R1 true)"
      by (simp add: wrR_def par_by_merge_seq_remove rpred merge_csp_do_right ex_unrest Healthy_if closure assms unrest usubst)
    also have "... = (\<not>\<^sub>r (\<exists> $ref\<acute>;$st\<acute> \<bullet> RR(\<not>\<^sub>r pre\<^sub>R P)) ;; R1 true)"
      by (rel_auto)
    also have "... = (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true)"
      by (simp add: Healthy_if closure ex_unrest unrest assms)
    also have "... = pre\<^sub>R P"
      by (simp add: NCSP_implies_NSRD NSRD_neg_pre_unit R1_preR assms rea_not_not)
    finally show ?thesis .
  qed
  have 2: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<lbrakk>1\<^sub>L|{}|0\<^sub>L\<rbrakk>\<^sup>I \<Phi>(true,id,\<langle>\<rangle>) = 
           (\<^bold>\<exists> ref\<^sub>0 \<bullet> (peri\<^sub>R P)\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = peri\<^sub>R P \<lbrakk>1\<^sub>L|{}|0\<^sub>L\<rbrakk>\<^sup>I \<Phi>(true,id,\<langle>\<rangle>)"
      by (simp add: SRD_peri_under_pre closure assms unrest)
    also have "... = (\<exists> $st\<acute> \<bullet> (peri\<^sub>R P \<parallel>\<^bsub> N\<^sub>C 1\<^sub>L {} 0\<^sub>L\<^esub> \<Phi>(true,id,\<langle>\<rangle>)))"
      by (simp add: CSPInterMerge_def par_by_merge_def seqr_exists_right)
    also have "... = 
         (\<exists> $st\<acute> \<bullet> \<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
            [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<exists> $st\<acute> \<bullet> RR(peri\<^sub>R P)) \<and>
             $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright> \<and> [\<guillemotleft>trace\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>]\<^sub>t \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &\<Sigma> \<oplus> \<guillemotleft>id\<guillemotright>($st)\<^sub>a on &\<emptyset>)"
      by (simp add: merge_csp_do_right assms Healthy_if assms closure rpred unrest ex_unrest)
    also have "... = 
         (\<^bold>\<exists> ref\<^sub>0 \<bullet> (\<exists> $st\<acute> \<bullet> RR(peri\<^sub>R P))\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)"
      by (rel_auto)
    also have "... = ?rhs"
      by (simp add: closure ex_unrest Healthy_if unrest assms)
    finally show ?thesis .
  qed
  have 3: "(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) \<lbrakk>1\<^sub>L|{}|0\<^sub>L\<rbrakk>\<^sup>F \<Phi>(true,id,\<langle>\<rangle>) = post\<^sub>R(P)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = post\<^sub>R P \<lbrakk>1\<^sub>L|{}|0\<^sub>L\<rbrakk>\<^sup>F \<Phi>(true,id,\<langle>\<rangle>)"
      by (simp add: SRD_post_under_pre closure assms unrest)
    also have "... = (\<^bold>\<exists> (st\<^sub>0, t\<^sub>0) \<bullet> 
                        [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> RR(post\<^sub>R P) \<and>
                        [\<guillemotleft>trace\<guillemotright> =\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright>]\<^sub>t \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &\<Sigma> \<oplus> \<guillemotleft>id\<guillemotright>($st)\<^sub>a on &\<emptyset>)"
      by (simp add: FinalMerge_csp_do_right assms closure unrest rpred Healthy_if)
    also have "... = RR(post\<^sub>R(P))"
      by (rel_auto)
    finally show ?thesis
      by (simp add: Healthy_if assms closure)
  qed
  show ?thesis
  proof -
    have "C2(P) = \<^bold>R\<^sub>s (\<Phi>(true,id,\<langle>\<rangle>) wr[1\<^sub>L|{}|0\<^sub>L]\<^sub>C pre\<^sub>R P \<turnstile>
          (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<lbrakk>1\<^sub>L|{}|0\<^sub>L\<rbrakk>\<^sup>I \<Phi>(true,id,\<langle>\<rangle>) \<diamondop> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) \<lbrakk>1\<^sub>L|{}|0\<^sub>L\<rbrakk>\<^sup>F \<Phi>(true,id,\<langle>\<rangle>))"
      by (simp add: C2_def, rdes_simp cls: assms, simp add: id_def)
    also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
      by (simp add: 1 2 3)
    finally show ?thesis .
  qed
qed

lemma Skip_C2_closed [closure]: 
  "Skip is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst)
  apply (simp add: rdes_def)
done
  
lemma ref_down_CRR [closure]:
  assumes "P is NCSP"
  shows "(\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) is CRR"
proof -
  have "(\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) = 
        (\<^bold>\<exists> ref\<^sub>0 \<bullet> (CRR(peri\<^sub>R P))\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)"
    by (simp add: Healthy_if assms closure)
  also have "... = CRR(\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)"
    by (rel_auto)
  finally show ?thesis
    by (simp add: Healthy_def')
qed
  
lemma C2_idem: 
  assumes "P is NCSP"
  shows "C2(C2(P)) = C2(P)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> (pre\<^sub>R P \<Rightarrow>\<^sub>r (\<^bold>\<exists> ref\<^sub>0' \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0'\<guillemotright>/$ref\<acute>\<rbrakk> \<and> \<guillemotleft>ref\<^sub>0\<guillemotright> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0'\<guillemotright>)) \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
    by (simp add: C2_form closure unrest rdes SRD_post_under_pre SRD_peri_under_pre usubst NCSP_rdes_intro assms)
  also have 
    "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> (\<^bold>\<exists> ref\<^sub>0' \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0'\<guillemotright>/$ref\<acute>\<rbrakk> \<and> \<guillemotleft>ref\<^sub>0\<guillemotright> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0'\<guillemotright>) \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
     by (rel_auto)
  also have 
    "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
    by (rel_auto)
  also have "... = C2(P)"
    by (simp add: C2_form closure unrest assms)
  finally show ?thesis .
qed  
  
lemma Stop_C2_closed [closure]: 
  "Stop is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst)
  apply (rel_auto)
done

lemma Miracle_C2_closed [closure]: 
  "Miracle is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst)
  apply (simp add: rdes_def)
done

lemma Chaos_C2_closed [closure]: 
  "Chaos is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst unrest)
  apply (simp add: rdes_def)
  apply (rel_auto)
done
  
(* An attempt at proving that the precondition of Chaos is false *)
  
lemma 
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "P wr[ns1|cs|ns2]\<^sub>C false = undefined" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
                   [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> R1 true \<and>
                   [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
                   $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
                   $tr \<le>\<^sub>u $tr\<acute> \<and>
                   &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> 
                   $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2) ;;
                    R1 true)"
    by (simp add: wrR_def par_by_merge_seq_remove CSPInnerMerge_form assms closure usubst unrest)
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (tt\<^sub>0, tt\<^sub>1) \<bullet>                    
                   [$tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
                   $tr \<le>\<^sub>u $tr\<acute> \<and>
                   &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) ;;
                    R1 true)"
    by (rel_blast)  
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (tt\<^sub>0, tt\<^sub>1) \<bullet>                    
                   [$tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(P) \<and>
                   $tr \<le>\<^sub>u $tr\<acute> \<and>
                   &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) ;;
                    R1 true)"
    by (simp add: Healthy_if assms)
oops      
      
  
(*  
lemma CSP5_Skip [closure]: "Skip is CSP5"
  unfolding CSP5_def Healthy_def
  by (rule SRD_eq_intro)
     (simp_all add: ParCSP_expand rdes closure wp rpred, rel_auto+)

lemma wppR_rea_true [wp]: "P wr\<^sub>R(M) true\<^sub>r = true\<^sub>r"
  by (simp add: wrR_def)
    
lemma CSP5_Stop [closure]: "Stop is CSP5"
  unfolding CSP5_def Healthy_def
  by (rule SRD_eq_intro)
     (simp_all add: ParCSP_expand rdes closure wp rpred, rel_auto)
*)  
   
subsection {* Failures-Divergences Semantics *}

definition divergences :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> '\<phi> list set" ("dv\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "divergences P s = {t | t. `(\<not>\<^sub>r pre\<^sub>R(P))\<lbrakk>(\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>)\<^sub>u/{$st,$tr,$tr\<acute>}\<rbrakk>`}"
  
definition traces :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<sigma>) set" ("tr\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "traces P s = {(t,s') | t s'. `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>`}"

definition failures :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<phi> set) set" ("fl\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "failures P s = {(t,r) | t r. `(pre\<^sub>R(P) \<and> peri\<^sub>R(P))\<lbrakk>\<guillemotleft>r\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$tr,$tr\<acute>\<rbrakk>`}"

(*
lemma bij_lens_in_out:
  "bij_lens (in\<alpha> +\<^sub>L out\<alpha>)"
  by (simp add: bij_lens_equiv_id lens_equiv_sym alpha_in_out)
  
lemma bij_lens_comp: "\<lbrakk> bij_lens X; bij_lens Y \<rbrakk> \<Longrightarrow> bij_lens (X ;\<^sub>L Y)"
  by (unfold_locales, simp_all add: lens_comp_def)
  
    
lemma   
  assumes "bij_lens X"
  shows "bij_lens ((X ;\<^sub>L fst\<^sub>L) +\<^sub>L (X ;\<^sub>L snd\<^sub>L))"
proof -
  have "X \<approx>\<^sub>L 1\<^sub>L"
    

lemma 
  assumes "P is NCSP" "Q is NCSP" "\<And> s. divergences P s \<subseteq> divergences Q s"
  shows "pre\<^sub>R(Q) \<sqsubseteq> pre\<^sub>R(P)"
proof (rule refine_by_obs[of "{$st,$tr,$tr\<acute>}\<^sub>\<alpha>" "{$ok,$ok\<acute>,$wait,$wait\<acute>,$st\<acute>,$ref,$ref\<acute>}\<^sub>\<alpha>"],
       simp_all add: unrest assms closure)
  oops
*)  
   
lemma traces_Skip:
  "tr\<lbrakk>Skip\<rbrakk>s = {([], s)}"
  by (simp add: traces_def rdes alpha closure, rel_simp)

lemma failures_Skip:
  "fl\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_Skip:
  "dv\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma traces_AssignsCSP:
  "tr\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {([], \<sigma>(s))}"
  by (simp add: traces_def rdes closure usubst alpha, rel_auto)

lemma failures_AssignsCSP:
  "fl\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_AssignsCSP:
  "dv\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma "fl\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: failures_def rdes closure usubst)

lemma "dv\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: divergences_def rdes closure usubst)

lemma "dv\<lbrakk>Chaos\<rbrakk>s = UNIV"
  by (simp add: divergences_def rdes, rel_auto)

lemma "tr\<lbrakk>Chaos\<rbrakk>s = {}"
  by (simp add: traces_def rdes closure usubst)

subsection {* Deadlock Freedom *}
  
definition DF :: "'e set \<Rightarrow> ('s, 'e) action" where
"DF(A) = (\<mu>\<^sub>C X \<bullet> (\<Sqinter> a\<in>A \<bullet> a \<^bold>\<rightarrow> Skip) ;; X)"
 
lemma DF_CSP [closure]: "A \<noteq> {} \<Longrightarrow> DF(A) is CSP"
  by (simp add: DF_def closure unrest)
  
(*
lemma preR_DF [rdes]:
  "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(DF(A)) = true\<^sub>r"
  by (simp add: DF_def rdes closure unrest wp usubst)
      
lemma periR_DF_lemma:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "(\<Sqinter> a \<in> A \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<^bold>^ i ;; P = 
         ($tr \<le>\<^sub>u $tr\<acute> \<and> elems\<^sub>u(&tt) \<subseteq>\<^sub>u \<guillemotleft>A\<guillemotright> \<and> #\<^sub>u(&tt) =\<^sub>u \<guillemotleft>i\<guillemotright> \<and> $st\<acute> =\<^sub>u $st) ;; P"
proof (induct i)
  case 0
  with assms show ?case
    apply (simp, rel_auto)
    apply (metis (no_types, hide_lams) list.set(1) minus_cancel order_bot_class.bot.extremum order_refl)
    apply (metis (no_types, lifting) less_eq_list_def strict_prefix_diff_minus)
  done
next
  case (Suc i)
  show ?case 
    apply (simp add: seqr_assoc[THEN sym] seq_UINF_distr tr_extend_seqr unrest usubst Suc)
    apply (rel_auto)
    apply (rename_tac tr st ok wait tr' st' ref x ok' wait' tr'' ref')
    apply (rule_tac x="ok'" in exI)
    apply (rule_tac x="wait'" in exI)
     apply (rule_tac x="tr''" in exI)
    apply (auto)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
      apply (metis append_Cons append_Nil append_minus list_concat_minus_list_concat subsetCE)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
    apply (metis append_Cons append_Nil append_minus list_concat_minus_list_concat)      
    apply (rename_tac tr st ok wait tr' st' ref ok' wait' tr'' ref')
    apply (rule_tac x="hd(tr'' - tr)" in exI)
    apply (auto)
    apply (rule_tac x="ok'" in exI)
     apply (rule_tac x="wait'" in exI)
     apply (rule_tac x="tr''" in exI)      
    apply (auto)
    apply (metis Prefix_Order.Cons_prefix_Cons Prefix_Order.Nil_prefix Prefix_Order.same_prefix_prefix hd_Cons_tl length_greater_0_conv less_eq_list_def prefix_concat_minus zero_less_Suc)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
    apply (metis Suc_length_conv append_Cons append_Nil append_minus hd_Cons_tl list.distinct(1) list_concat_minus_list_concat set_subset_Cons subsetCE)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
    apply (metis Suc_length_conv append_Nil append_one_prefix cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc length_drop list.sel(1) list.size(3) list_concat_minus_list_concat minus_list_def nth_Cons_0 prefix_code(1) zero_less_Suc)
    apply (metis contra_subsetD hd_in_set length_greater_0_conv zero_less_Suc)
  done
qed

lemma periR_DF [rdes]:
  "A \<noteq> {} \<Longrightarrow> peri\<^sub>R(DF(A)) = ($tr \<le>\<^sub>u $tr\<acute> \<and> elems\<^sub>u(&tt) \<subseteq>\<^sub>u \<guillemotleft>A\<guillemotright> \<and> (\<^bold>\<exists> a \<in> \<guillemotleft>A\<guillemotright> \<bullet> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>))"
  apply (simp add: DF_def rdes closure unrest wp usubst alpha)  
  apply (simp add: seq_UINF_distr periR_DF_lemma unrest)
  apply (rel_auto)
 oops
    
lemma postR_DF [rdes]:
  "A \<noteq> {} \<Longrightarrow> post\<^sub>R(DF(A)) = false"
  oops
  
  
text {* Example deadlock freedom proof *}
  
lemma "DF(UNIV) \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> (a \<^bold>\<rightarrow> Skip) ;; X)"
  apply (rule_tac mu_csp_basic_refine)
  apply (simp_all add: closure rdes wp usubst alpha)
  oops
*)
    
(*
  apply (rel_auto)
  apply (rel_blast)
    oops    
*)
subsection {* CSP Action Type and Lifted Definitions *}
   
typedef ('s, 'e) Action = "{P :: ('s, 'e) action. P is NCSP}"
  by (rule_tac x="Skip" in exI, simp add: closure)
    
setup_lifting type_definition_Action
  
lift_definition skip :: "('s, 'e) Action" is Skip
  by (simp add: closure)
    
lift_definition stop :: "('s, 'e) Action" is Stop
  by (simp add: closure)

lift_definition seqCircus :: "('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" (infixr ";\<^sub>C" 71)
  is "op ;;"
  by (simp add: closure)
   
lemma stop_left_zero: "stop ;\<^sub>C P = stop"
  by (transfer, simp add: NCSP_implies_CSP Stop_left_zero)
    
instantiation Action :: (type, type) order
begin
  lift_definition less_eq_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "op \<le>" .
  lift_definition less_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "op <" .
instance by (intro_classes) (transfer, simp add: less_uexpr_def)+
end
  
instance Action :: (type, type) refine ..

instantiation Action :: (type, type) complete_lattice
begin
  lift_definition sup_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> ('a, 'b) Action" is Lattices.sup
    by (simp add: closure)
  lift_definition inf_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> ('a, 'b) Action" 
    is "\<lambda> P Q. P \<^bold>\<squnion>\<^bsub>TCSP\<^esub> Q" by simp
  lift_definition bot_Action :: "('a, 'b) Action" is Miracle
    by (simp add: closure)
  lift_definition top_Action :: "('a, 'b) Action" is Chaos
    by (simp add: closure)
  lift_definition Sup_Action :: "('a, 'b) Action set \<Rightarrow> ('a, 'b) Action" 
    is "\<lambda> A. \<^bold>\<Sqinter>\<^bsub>TCSP\<^esub> A"
    by (rule csp_theory.weak.inf_closed, auto)
  lift_definition Inf_Action :: "('a, 'b) Action set \<Rightarrow> ('a, 'b) Action"
    is "\<lambda> A. \<^bold>\<Squnion>\<^bsub>TCSP\<^esub> A" 
    by (rule csp_theory.weak.sup_closed, auto)
instance 
  apply (intro_classes)
             apply (transfer, simp add: csp_theory.join_left)
            apply (transfer, simp add: csp_theory.join_right)
           apply (transfer, simp add: csp_theory.join_le)
          apply (transfer, simp add: csp_theory.meet_left)
         apply (transfer, simp add: csp_theory.meet_right)
        apply (transfer, simp add: csp_theory.meet_le)
       apply (transfer, metis csp_theory.sup_upper mem_Collect_eq subsetI tcsp_hcond_def utp_order_carrier)
      apply (transfer, force intro: csp_theory.sup_least)
     apply (transfer, simp add: Ball_Collect csp_theory.inf_lower)
    apply (transfer, force intro: csp_theory.inf_greatest)
   apply (transfer, metis (full_types) csp_bottom_Chaos csp_theory.eq_is_equal csp_theory.weak_sup_empty)
  apply (transfer, metis (full_types) csp_top_Miracle csp_theory.eq_is_equal csp_theory.weak_inf_empty)
done
    
end
  
(*
type_synonym ('s, 'e) crel = "('e list, ('s, ('e, unit) csp_vars_scheme) rsp_vars_scheme) rrel"

lift_definition preC :: "('s, 'e) action \<Rightarrow> ('s, 'e) crel" ("pre\<^sub>C") is 
  "\<lambda> P. (\<exists> $wait\<acute> \<bullet> R2(pre\<^sub>R P)) :: ('s, 'e) action"
  by (auto simp add: unrest closure, (rel_auto)+)

lift_definition periC :: "('s, 'e) action \<Rightarrow> ('s, 'e) crel" ("peri\<^sub>C") is 
  "(R2 \<circ> peri\<^sub>R) :: ('s, 'e) action \<Rightarrow> ('s, 'e) action"
  by (simp_all add: unrest closure, rel_auto)

lift_definition postC :: "('s, 'e) action \<Rightarrow> ('s, 'e) crel" ("post\<^sub>C") is 
  "(R2 \<circ> post\<^sub>R) :: ('s, 'e) action \<Rightarrow> ('s, 'e) action"
  by (simp_all add: unrest closure, rel_auto)

lift_definition wpC :: "('s, 'e) crel \<Rightarrow> ('s, 'e) crel \<Rightarrow> ('s, 'e) crel" (infix "wp\<^sub>C" 60) is "wpR"
  by (auto simp add: unrest closure SRD_healths wpR_def)
    
lift_definition rdes :: "('s, 'e) crel \<Rightarrow> ('s, 'e) crel \<Rightarrow> ('s, 'e) crel \<Rightarrow> ('s, 'e) action" is
"\<lambda> P Q R. \<^bold>R\<^sub>s(P wp\<^sub>R false \<turnstile> (Q ;; ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S)) \<diamondop> R)" .
    
lemma R2_implies_R2c [closure]: "P is R2 \<Longrightarrow> P is R2c"
  by (rel_blast)
    
lemma tr'_minus_tr_is_R2c [closure]: "$tr\<acute> =\<^sub>u $tr is R2c"
  by (simp add: Healthy_def' R2c_tr'_minus_tr)
    
lemma rea_lift_is_R2c [closure]: "\<lceil>P\<rceil>\<^sub>R is R2c"
  by (rel_auto)
    
lemma unrest_out_var_rea_true [unrest]:
  "x \<bowtie> tr \<Longrightarrow> $x\<acute> \<sharp> R1(true)"
  by (rel_auto, simp_all add: lens_indep_def)
    
lemma unrest_st'_tr_ident [unrest]:
  "$st\<acute> \<sharp> ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S)"
  by (rel_auto)
    
lemma rdes_NSRD [closure]: "rdes P Q R is NSRD"
  apply (transfer, auto)
  apply (rule NSRD_intro)
  apply (rule RHS_tri_design_is_SRD)
  apply (simp_all add: wpR_def rea_pre_RHS_design rea_peri_RHS_design seqr_assoc[THEN sym] usubst 
         R2c_true R1_R2c_seqr_distribute R1_rea_not' R2c_rea_not R2c_rea_impl R1_rea_impl' rpred 
         closure unrest)
done
    
named_theorems rrel_lift
  
thm inf_rrel.rep_eq
thm sup_rrel.rep_eq
  
lemma rrel_lift_laws_1 [rrel_lift]: 
  "\<lceil>R1 true\<rceil>\<^sub>r = true" "\<lceil>false\<rceil>\<^sub>r = false"
  by (simp_all add: bot_rrel.abs_eq top_rrel.abs_eq upred_defs inf_rrel_def)      

thm Abs_rrel_inverse
    
lemma Abs_rrel_inv [rrel_lift]: 
  "\<lbrakk> P is R2; $ok \<sharp> P; $ok\<acute> \<sharp> P; $wait \<sharp> P; $wait\<acute> \<sharp> P \<rbrakk> \<Longrightarrow> Rep_rrel \<lceil>P\<rceil>\<^sub>r = P"
  by (simp add: Abs_rrel_inverse)
    
lemma rrel_lift_laws_2 [rrel_lift]:
  assumes 
    "P is R2" "Q is R2" 
    "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q" "$wait \<sharp> Q" "$wait\<acute> \<sharp> Q"
  shows "\<lceil>P \<and> Q\<rceil>\<^sub>r = (\<lceil>P\<rceil>\<^sub>r \<and> \<lceil>Q\<rceil>\<^sub>r)" "\<lceil>P \<or> Q\<rceil>\<^sub>r = (\<lceil>P\<rceil>\<^sub>r \<or> \<lceil>Q\<rceil>\<^sub>r)"
  by (simp_all add: upred_defs inf_rrel_def sup_rrel_def, simp_all add: Abs_rrel_inv assms closure)

lemma preC_unfold [rdes]: "P is NSRD \<Longrightarrow> pre\<^sub>C(P) = \<lceil>pre\<^sub>R(P)\<rceil>\<^sub>r"
  by (simp add: preC_def Healthy_if closure ex_unrest unrest)

lemma periC_unfold [rdes]: "P is NSRD \<Longrightarrow> peri\<^sub>C(P) = \<lceil>peri\<^sub>R(P)\<rceil>\<^sub>r"
  by (simp add: periC_def Healthy_if closure ex_unrest unrest)

lemma postC_unfold [rdes]: "P is NSRD \<Longrightarrow> post\<^sub>C(P) = \<lceil>post\<^sub>R(P)\<rceil>\<^sub>r"
  by (simp add: postC_def Healthy_if closure ex_unrest unrest)

lemma preC_skip [rdes]: "pre\<^sub>C(Skip) = true"
  by (simp add: rdes rrel_lift closure)

lemma periC_skip [rdes]: "peri\<^sub>C(Skip) = false"
  by (simp add: rdes rrel_lift closure)
    
lemma wpR_R2_closed [closure]: 
  "\<lbrakk> P is R2; Q is R2 \<rbrakk> \<Longrightarrow> P wp\<^sub>R Q is R2"
  by (simp add: wpR_def closure)

lemma unrest_wpR_1 [unrest]:
  "\<lbrakk> x \<bowtie> tr; $x \<sharp> P \<rbrakk> \<Longrightarrow> $x \<sharp> P wp\<^sub>R Q"
  by (simp add: wpR_def unrest)

lemma unrest_wpR_2 [unrest]:
  "\<lbrakk> x \<bowtie> tr; $x\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P wp\<^sub>R Q"
  by (simp add: wpR_def unrest)
    
lemma preC_seq [rdes]:
  "\<lbrakk> P is NSRD; Q is NSRD \<rbrakk> \<Longrightarrow> pre\<^sub>C(P ;; Q) = (pre\<^sub>C P \<and> post\<^sub>C P wp\<^sub>C pre\<^sub>C Q)"
  by (simp add: rdes rrel_lift SRD_healths closure unrest wpC_def)
    
lemma periC_seq [rdes]:
  "\<lbrakk> P is NSRD; Q is NSRD \<rbrakk> \<Longrightarrow> peri\<^sub>C(P ;; Q) = (pre\<^sub>C P \<and> post\<^sub>C P wp\<^sub>C pre\<^sub>C Q)"
*) 
  
end