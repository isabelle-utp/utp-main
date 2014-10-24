(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_iteration.thy                                              *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Iteration *}

theory utp_alpha_iteration
imports 
  utp_alpha_pred
  utp_alpha_rel
  "../core/utp_iteration"
  "../laws/utp_alpha_laws"
  "../parser/utp_alpha_pred_parser"
(*  "../theories/utp_context" *)
begin

default_sort TYPED_MODEL

instantiation uapred :: (TYPED_MODEL) star_op
begin

lift_definition star_uapred :: "'a uapred \<Rightarrow> 'a uapred"
is "\<lambda> (a, p). (a, ((p\<^sup>\<star>) ;\<^sub>R II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub>) :: 'a upred)"
  apply (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (metis Compl_eq_Diff_UNIV UNREST_StarP_coerce VAR_def)
done

instance ..

end

syntax
  "_n_uapred_star"     :: "n_uapred \<Rightarrow> n_uapred" ("_\<^sup>\<star>" [900] 900)

translations
  "_n_uapred_star p"   == "p\<^sup>\<star>"

lemma StarA_alphabet [alphabet]: "\<alpha>(P\<^sup>\<star>) = \<alpha>(P)"
  apply (simp add:pred_alphabet_def star_uapred.rep_eq)
  apply (metis (lifting) fst_def prod.exhaust split_conv)
done

lemma StarA_closure [closure]: 
  "P \<in> WF_ALPHA_REL \<Longrightarrow> P\<^sup>\<star> \<in> WF_ALPHA_REL"
  by (metis StarA_alphabet WF_ALPHA_REL_def mem_Collect_eq)

lemma EvalA_StarA [evala]:
  "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<pi> = (\<lbrakk>P\<rbrakk>\<pi>\<^sup>\<star>) ;\<^sub>R II\<^bsub>\<langle>\<alpha>(P)\<rangle>\<^sub>f\<^esub>"
  apply (case_tac P)
  apply (auto simp add:star_uapred.rep_eq EvalA_def WF_ALPHA_PREDICATE_def
WF_PREDICATE_OVER_def pred_alphabet_def)
done


lemma StarA_unfold:
  "``P\<^sup>\<star>`` = ``(P ; P\<^sup>\<star>) \<or> II\<^bsub>\<alpha>(P)\<^esub>``"
  apply (utp_alpha_tac)
  apply (subst left_pre_kleene_algebra_class.star_unfoldl_eq[THEN sym])
  apply (simp add:plus_upred_def times_upred_def one_upred_def)
  apply (rule)
  apply (metis alphabet_split inf_sup_aci(7) sup.idem sup_commute)
  apply (metis (hide_lams, no_types) OrP_comm SemiR_OrP_distr SemiR_SkipR_left SemiR_assoc)
done

definition 
  IterA :: " 'a uapred 
           \<Rightarrow> 'a uapred 
           \<Rightarrow> 'a uapred"  where
"IterA b P \<equiv> ((b \<and>\<^sub>\<alpha> P)\<^sup>\<star>) \<and>\<^sub>\<alpha> (\<not>\<^sub>\<alpha> b\<acute>)"  

syntax
  "_n_uapred_while"    :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("while _ do _ od")

translations
  "_n_uapred_while b p"   == "CONST IterA b p"

lemma EvalA_IterA_basic [evala]: "\<lbrakk>IterA b P\<rbrakk>\<pi> = \<lbrakk>((b \<and>\<^sub>\<alpha> P)\<^sup>\<star>) \<and>\<^sub>\<alpha> (\<not>\<^sub>\<alpha> b\<acute>)\<rbrakk>\<pi>"
  by (simp add:IterA_def)

lemma IterA_alphabet [alphabet]: "\<lbrakk> \<alpha>(b) |\<subseteq>| \<alpha>(P); \<alpha>(P) \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> \<alpha>(IterA b P) = \<alpha>(P)"
  apply (auto elim!:fsubset_elim simp add: IterA_def alphabet fmember.rep_eq)
  apply (metis HOMOGENEOUS_HOM_ALPHA SS_DASHED_app SS_UNDASHED_app SS_dash_DASHED SS_ident_app dash_UNDASHED_image dash_inv_into hom_alphabet_dash hom_alphabet_undash inv_into_into set_rev_mp)
done

lemma IterA_false: 
  "\<lbrakk> A |\<subseteq>| \<alpha>(P); \<alpha>(P) \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> ``while false\<^bsub>A\<^esub> do P od`` = ``II\<^bsub>\<alpha>(P)\<^esub>``"
  by (utp_alpha_tac)

lemma IterA_true: 
  "\<lbrakk> A |\<subseteq>| \<alpha>(P); \<alpha>(P) \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> ``while true\<^bsub>A\<^esub> do P od`` = ``false\<^bsub>\<alpha>(P)\<^esub>``"
  by (utp_alpha_tac)

theorem IterA_cond_true:
  assumes "b \<in> COND" "P \<in> REL" "\<alpha>(b) |\<subseteq>| \<alpha>(P)" "\<alpha>(P) \<in> HOM_ALPHABET"
  shows "``(while b do P od) \<and> b`` = ``(P \<and> b) ; while b do P od``"
proof -
  have "``while b do P od \<and> b`` = ``((b \<and> P)\<^sup>\<star> \<and> \<not>b\<acute>) \<and> b``"
    by (simp add:IterA_def)

  also have "... = ``((((b \<and> P) ; (b \<and> P)\<^sup>\<star>) \<or> II\<^bsub>\<alpha>(P)\<^esub>) \<and> \<not>b\<acute>) \<and> b``"
    by (metis AndA_alphabet StarA_unfold assms(3) fsubseteq_union1)

  also have "... = ``(b \<and> (((b \<and> P) ; (b \<and> P)\<^sup>\<star>) \<or> II\<^bsub>\<alpha>(P)\<^esub>)) \<and> \<not>b\<acute>``"
    by (metis AndA_assoc AndA_comm)

  also have "... = ``((b \<and> II\<^bsub>\<alpha>(P)\<^esub>) \<or> (b \<and> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>``"
    by (metis AndA_OrA_distl OrA_comm)

  also have "... = ``(((b \<and> II\<^bsub>\<alpha>(P)\<^esub>) \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>``"
  proof -
    have "out\<alpha> b |\<subseteq>| out\<alpha> ``(b \<and> P)\<^sup>\<star>``"
      by (rule fsubset_intro, simp add:var_dist alphabet)

    with assms show ?thesis
      by (metis (lifting, no_types) AndA_WF_ALPHA_REL AndA_assoc AndA_idem SemiA_AndA_left_precond StarA_closure WF_ALPHA_COND_WF_ALPHA_REL)
  qed

  also from assms have "... = ``(((II\<^bsub>\<alpha>(P)\<^esub> \<and> b\<acute>) \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>``"
    by (metis REL_ALPHABET_WF_ALPHA_REL SkipA_AndA_cond)

  also have "... = ``(((II\<^bsub>\<alpha>(P)\<^esub> \<and> b\<acute> \<and> \<not>b\<acute>) \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>``"
    by (metis (lifting, no_types) AndA_OrA_distr AndA_assoc AndA_idem)

  also from assms have "... = ``((b \<and> P) ; (b \<and> P)\<^sup>\<star>) \<and> \<not>b\<acute>``"
    apply (simp)
    apply (subst OrA_left_unit_sub)
    apply (auto elim!:fmember_elim fnmember_elim intro!:fmember_intro simp add:alphabet assms var_dist)[1]
    apply (metis REL_ALPHABET_UNDASHED_DASHED UnE WF_ALPHA_REL_def assms(2) in_out_union mem_Collect_eq)
    apply (metis (no_types, hide_lams) HOMOGENEOUS_HOM_ALPHA HOM_ALPHABET_undash_out SS_DASHED_app SS_UNDASHED_app SS_VAR_RENAME_INV UNDASHED_undash_elim Un_iff VAR_RENAME_INV_app WF_ALPHA_COND_WF_ALPHA_REL WF_ALPHA_REL_unfold assms(1) assms(3) assms(4) contra_subsetD hom_alphabet_undash imageI less_eq_fset.rep_eq out_member)
    apply (simp)
  done

  also have "... = ``(b \<and> P) ; ((b \<and> P)\<^sup>\<star> \<and> \<not>b\<acute>)``"
  proof -
    (* FIXME: This proof is way longer than it should be. Need better support
       for primed alphabets. *)
    from assms have "\<langle>SS\<rangle>\<^sub>s ` \<langle>\<alpha> b\<rangle>\<^sub>f \<subseteq> \<langle>\<alpha> P\<rangle>\<^sub>f"
      apply (auto)
      apply (case_tac "xa \<in> D\<^sub>0")
      apply (simp add:urename)
      apply (metis HOMOGENEOUS_HOM_ALPHA contra_subsetD hom_alphabet_undash less_eq_fset.rep_eq)
      apply (subgoal_tac "xa \<in> D\<^sub>1")
      apply (simp add:urename)
      apply (rule HOMOGENEOUS_out_unprimed)
      apply (metis HOMOGENEOUS_HOM_ALPHA)
      apply (metis contra_subsetD less_eq_fset.rep_eq out_member)
      apply (metis Un_iff WF_ALPHA_COND_WF_ALPHA_REL WF_ALPHA_REL_unfold contra_subsetD)
    done

    with assms show ?thesis
      apply (subst SemiA_AndA_right_postcond)
      apply (simp add:assms closure)
      apply (simp add:alphabet var_dist)
      apply (metis HOM_ALPHABET_SS fimage_mono funion_absorb2 funion_upper2 in_alphabet_union)
      apply (metis in_vars_union subset_Un_eq)
    done
  qed

  finally show ?thesis
    by (metis AndA_comm IterA_def)
qed

theorem IterA_cond_false:
  assumes "b \<in> COND" "P \<in> REL" "\<alpha>(b) |\<subseteq>| \<alpha>(P)" "\<alpha>(P) \<in> HOM_ALPHABET"
  shows "``while b do P od \<and> \<not>b`` = ``II\<^bsub>\<alpha>(P)\<^esub> \<and> \<not>b``"
proof -
  have "``while b do P od \<and> \<not>b`` = ``((b \<and> P)\<^sup>\<star> \<and> \<not>b\<acute>) \<and> \<not>b``"
    by (simp add:IterA_def)

  also have "... = ``((((b \<and> P) ; (b \<and> P)\<^sup>\<star>) \<or> II\<^bsub>\<alpha>(P)\<^esub>) \<and> \<not>b\<acute>) \<and> \<not>b``"
    by (metis (hide_lams, no_types) StarA_unfold AndA_alphabet assms(3) fsubseteq_union1)

  also have "... = ``(\<not>b \<and> (((b \<and> P) ; (b \<and> P)\<^sup>\<star>)  \<or> II\<^bsub>\<alpha>(P)\<^esub>)) \<and> \<not>b\<acute>``"
    by (metis AndA_assoc AndA_comm)
  also have "... = ``(((\<not>b \<and> (b \<and> P)) ; (b \<and> P)\<^sup>\<star>) \<or> (\<not>b \<and> II\<^bsub>\<alpha>(P)\<^esub>)) \<and> \<not>b\<acute>``"
    sledgehammer
    apply (subst AndA_OrA_distl)
    apply (subst SemiA_AndA_left_precond[THEN sym])
    apply (simp add:assms closure)
    apply (simp add:alphabet)
    apply (metis out_alphabet_union sup_ge1)
    apply (simp add:assms alphabet var_dist closure fmember.rep_eq)
  done

  also from assms have "... = ``(\<not>b \<and> II\<^bsub>\<alpha>(P)\<^esub>) \<and> \<not>b\<acute>``"
    apply (subst AndA_assoc)
    apply (subst AndA_comm)
    apply (simp add:AndA_contra AndA_left_zero SemiA_FalseA_left assms closure alphabet fsubseteq_union1  OrA_left_unit_sub)
  done

  also have "... = ``(\<not>b \<and> II\<^bsub>\<alpha>(P)\<^esub>)``"
    apply (subst AndA_assoc[THEN sym])
    apply (subst SkipA_AndA_post)
    apply (simp_all add:closure assms alphabet)
    apply (metis HOM_ALPHABET_SS assms(3) assms(4) subset_fimage_iff)
    apply (simp add:urename closure assms)
    apply (metis AndA_assoc AndA_idem)
  done
    
  finally show ?thesis
    by (metis AndA_comm) 
qed

theorem IterA_unfold:
  assumes "b \<in> COND" "P \<in> REL" "\<alpha>(b) |\<subseteq>| \<alpha>(P)" "\<alpha>(P) \<in> HOM_ALPHABET"
  shows "``while b do P od`` = ``(P ; while b do P od) \<lhd> b \<rhd> II\<^bsub>\<alpha>(P)\<^esub>``"
proof -
  have "``while b do P od`` = ``(while b do P od \<and> b) \<or> (while b do P od \<and> \<not>b)``"
    by (metis AndA_comm IterA_alphabet WF_ALPHA_PRED_cases assms)

  also have "... = ``((P \<and> b) ; while b do P od) \<or> (II\<^bsub>\<alpha>(P)\<^esub> \<and> \<not>b)``"
    by (metis IterA_cond_false IterA_cond_true assms(1) assms(2) assms(3) assms(4))

  also from assms have "... = ``(P ; while b do P od) \<lhd> b \<rhd> II\<^bsub>\<alpha>(P)\<^esub>``"
    apply (subst AndA_comm)
    apply (subst SemiA_AndA_left_precond)
    apply (simp_all add:assms alphabet closure)
    apply (metis assms(3) fsubset_funion_eq out_alphabet_union)
    apply (metis AndA_comm CondA_alt_def)
  done

  finally show ?thesis .
qed

declare EvalA_IterA_basic [evala del]

lemma EvalA_IterA [evala]: 
  assumes "P \<in> REL" "b \<in> COND"
          "\<alpha>(P) \<in> HOM_ALPHABET" "\<alpha>(b) |\<subseteq>| \<alpha>(P)"
  shows "\<lbrakk>IterA b P\<rbrakk>\<pi> = (IterP \<lbrakk>b\<rbrakk>\<pi> \<lbrakk>P\<rbrakk>\<pi>) ;\<^sub>R II\<^bsub>\<langle>\<alpha>(P)\<rangle>\<^sub>f\<^esub>"
proof -
  from assms have "((((\<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>P\<rbrakk>\<pi>)\<^sup>\<star>) ;\<^sub>R II\<^bsub>\<langle>\<alpha> P\<rangle>\<^sub>f\<^esub>) \<and>\<^sub>p \<not>\<^sub>p \<lbrakk>b\<rbrakk>\<pi>\<acute>) = ((((\<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>P\<rbrakk>\<pi>)\<^sup>\<star>) \<and>\<^sub>p \<not>\<^sub>p \<lbrakk>b\<rbrakk>\<pi>\<acute>) ;\<^sub>R II\<^bsub>\<langle>\<alpha> P\<rangle>\<^sub>f\<^esub>)"
    apply (subst SemiR_AndP_right_postcond[THEN sym])
    apply (simp add:closure)
    apply (subst SkipRA_AndP_postcond)
    apply (metis HOMOGENEOUS_HOM_ALPHA)
    apply (rule UNREST_NotP)
    apply (rule UNREST_ConvR)
    apply (rule UNREST_subset[of "- D\<^sub>0  \<union> (- \<langle>\<alpha>(b)\<rangle>\<^sub>f)"])
    apply (rule UNREST_union)
    apply (metis UNREST_WF_CONDITION WF_ALPHA_COND_EvalA_WF_CONDITION assms(2))
    apply (metis UNREST_EvalA)
    apply (auto)
    apply (metis (no_types, hide_lams) HOMOGENEOUS_HOM_ALPHA SS_UNDASHED_app SS_VAR_RENAME_INV SS_ident_app UNDASHED_eq_dash_contra VAR_RENAME_INV_app contra_subsetD hom_alphabet_undash less_eq_fset.rep_eq out_member)
    apply (simp add:urename)
    apply (metis ConvR_NotP NotP_cond_closure SemiR_AndP_right_precond WF_ALPHA_COND_EvalA_WF_CONDITION)
  done

  thus ?thesis

  using assms
    apply (subgoal_tac "\<langle>\<alpha> b\<rangle>\<^sub>f \<union> \<langle>\<alpha> P\<rangle>\<^sub>f = \<langle>\<alpha> P\<rangle>\<^sub>f")
    apply (simp add:IterA_def evala IterP_def alphabet)
    apply (auto)
  done
qed

end


