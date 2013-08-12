(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_hoare.thy                                                        *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Hoare Logic *}

theory utp_hoare
imports 
  utp_lattice 
  utp_recursion
  "../laws/utp_pred_laws"
  "../laws/utp_rel_laws"
  "../laws/utp_refine_laws"
  "../parser/utp_pred_parser"
begin

definition HoareP :: 
  "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_{_}\<^sub>p_" [200,0,201] 200) where
"p{Q}\<^sub>pr = ((p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq>\<^sub>p Q)"

declare HoareP_def [eval,evalr,evalrx]

syntax
  "_upred_hoare" :: "upred \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" ("_{_}_" [55,0,56] 55)

translations
  "_upred_hoare p Q r"  == "CONST HoareP p Q r"

lemma HoareP_intro [intro]:
  "(p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q \<Longrightarrow> `p{Q}r`"
  by (metis HoareP_def less_eq_WF_PREDICATE_def)

lemma HoareP_elim [elim]:
  "\<lbrakk> `p{Q}r`; \<lbrakk> (p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis HoareP_def less_eq_WF_PREDICATE_def)

theorem HoareP_AndP:
  "`p{Q}(r \<and> s)` = `p{Q}r \<and> p{Q}s`"
  apply (simp add:HoareP_def urename)
  apply (utp_pred_auto_tac)
done

theorem HoareP_OrP:
  "`(p \<or> q){Q}r` = `p{Q}r \<and> q{Q}r`"
  apply (simp add:HoareP_def urename)
  apply (utp_pred_auto_tac)
done
  
theorem HoareP_SemiR:
  assumes 
    "p \<in> WF_CONDITION" "r \<in> WF_CONDITION" "s \<in> WF_CONDITION"
    "Q1 \<in> WF_RELATION" "Q2 \<in> WF_RELATION"
    "`p{Q1}s`" "`s{Q2}r`" 
  shows "`p{Q1 ; Q2}r`"
proof
  from assms 
  have refs: "(p \<Rightarrow>\<^sub>p s\<acute>) \<sqsubseteq> Q1" "(s \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q2"
    by (auto elim!:HoareP_elim)

  thus "`(p \<Rightarrow> r\<acute>)` \<sqsubseteq> `Q1 ; Q2`"
    apply (rule_tac order_trans)
    apply (rule SemiR_step_refine)
    apply (assumption)
    apply (assumption)
    apply (rule SemiR_spec_inter_refine)
    apply (simp_all add:assms)
  done
qed

end