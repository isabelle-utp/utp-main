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
begin

instantiation WF_ALPHA_PREDICATE :: (VALUE) star_op
begin

lift_definition star_WF_ALPHA_PREDICATE :: "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE"
is "\<lambda> (a, p). (a, ((p\<^sup>\<star>) ;\<^sub>R II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub>) :: 'a WF_PREDICATE)"
  apply (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (metis Compl_eq_Diff_UNIV UNREST_StarP_coerce VAR_def)
done

instance ..

end

lemma StarA_alphabet [alphabet]: "\<alpha>(P\<^sup>\<star>) = \<alpha>(P)"
  apply (simp add:pred_alphabet_def star_WF_ALPHA_PREDICATE.rep_eq)
  apply (metis (lifting) fst_def prod.exhaust split_conv)
done

lemma EvalA_StarA [evala]:
  "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<pi> = (\<lbrakk>P\<rbrakk>\<pi>\<^sup>\<star>) ;\<^sub>R II\<^bsub>\<langle>\<alpha>(P)\<rangle>\<^sub>f\<^esub>"
  apply (case_tac P)
  apply (auto simp add:star_WF_ALPHA_PREDICATE.rep_eq EvalA_def WF_ALPHA_PREDICATE_def
WF_PREDICATE_OVER_def pred_alphabet_def)
done

definition 
  IterA :: " 'a WF_ALPHA_PREDICATE 
           \<Rightarrow> 'a WF_ALPHA_PREDICATE 
           \<Rightarrow> 'a WF_ALPHA_PREDICATE"  where
"IterA b P \<equiv> ((b \<and>\<^sub>\<alpha> P)\<^sup>\<star>) \<and>\<^sub>\<alpha> (\<not>\<^sub>\<alpha> b\<acute>)"  

(*
lemma EvalA_IterA: 
  assumes "P \<in> WF_ALPHA_REL" "b \<in> WF_ALPHA_COND"
          "\<alpha>(P) \<in> HOM_ALPHABET" "\<alpha>(b) \<subseteq>\<^sub>f \<alpha>(P)"
  shows "\<lbrakk>IterA b P\<rbrakk>\<pi> = (IterP \<lbrakk>b\<rbrakk>\<pi> \<lbrakk>P\<rbrakk>\<pi>) ;\<^sub>R II\<^bsub>\<langle>\<alpha>(P)\<rangle>\<^sub>f\<^esub>"
proof -

  have "((((\<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>P\<rbrakk>\<pi>)\<^sup>\<star>) ;\<^sub>R II\<^bsub>\<langle>\<alpha> P\<rangle>\<^sub>f\<^esub>) \<and>\<^sub>p \<not>\<^sub>p \<lbrakk>b\<rbrakk>\<pi>\<acute>) = ((((\<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>P\<rbrakk>\<pi>)\<^sup>\<star>) \<and>\<^sub>p \<not>\<^sub>p \<lbrakk>b\<rbrakk>\<pi>\<acute>) ;\<^sub>R II\<^bsub>\<langle>\<alpha> P\<rangle>\<^sub>f\<^esub>)"
  proof -
    have "(((\<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>P\<rbrakk>\<pi>)\<^sup>\<star>) ;\<^sub>R II\<^bsub>\<langle>\<alpha> P\<rangle>\<^sub>f\<^esub> \<and>\<^sub>p \<not>\<^sub>p \<lbrakk>b\<rbrakk>\<pi>\<acute>) = (((\<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>P\<rbrakk>\<pi>)\<^sup>\<star>) ;\<^sub>R \<not>\<^sub>p \<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p II\<^bsub>\<langle>\<alpha> P\<rangle>\<^sub>f\<^esub>)"
      apply (subst SkipRA_AndP_postcond)
      apply (simp_all add:closure assms unrest urename)
      apply (rule UNREST_NotP)
      apply (rule UNREST_ConvR)
      apply (rule UNREST_subset)
      apply (rule EvalA_UNREST)
      apply (auto)
      apply (case_tac "xa \<in> D\<^sub>0")
      apply (simp add:urename)
      apply (insert assms)
      apply (subgoal_tac "xa\<acute> \<in> \<langle>\<alpha> P\<rangle>\<^sub>f")
      apply (force)
      apply (auto)
    sorry

    thus ?thesis
      sorry
  qed

  thus ?thesis

  using assms
    apply (subgoal_tac "\<langle>\<alpha> b\<rangle>\<^sub>f \<union> \<langle>\<alpha> P\<rangle>\<^sub>f = \<langle>\<alpha> P\<rangle>\<^sub>f")
    apply (simp add:IterA_def evala IterP_def alphabet)
    apply (auto)
  done
qed
*)

end


