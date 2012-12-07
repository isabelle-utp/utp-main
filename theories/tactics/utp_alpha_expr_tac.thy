(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_alpha_expr_tac.thy                                               *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Proof Tactic for Alphabetised Expressions *}

theory utp_alpha_expr_tac
imports "../alpha/utp_alpha_expr" utp_pred_tac utp_expr_tac utp_alpha_tac
begin

context ALPHA_PRED
begin

subsection {* Interpretation Function *}

definition EvalAE ::
  "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow>
   ('VALUE, 'TYPE) EXPRESSION" ("\<lbrakk>_\<rbrakk>\<alpha>\<epsilon>") where
"EvalAE e = \<epsilon> e"

subsection {* Transfer Theorems *}

theorem EvalAE_simp [evala] :
"\<lbrakk>e1 \<in> WF_ALPHA_EXPRESSION;
 e2 \<in> WF_ALPHA_EXPRESSION\<rbrakk> \<Longrightarrow>
 e1 = e2 \<longleftrightarrow> (\<alpha>\<epsilon> e1) = (\<alpha>\<epsilon> e2) \<and> \<lbrakk>e1\<rbrakk>\<alpha>\<epsilon> = \<lbrakk>e2\<rbrakk>\<alpha>\<epsilon>"
apply (simp add: EvalAE_def)
apply (simp add: prod_eq_iff)
done

theorem EvalAE_intro :
"\<lbrakk>e1 \<in> WF_ALPHA_EXPRESSION;
 e2 \<in> WF_ALPHA_EXPRESSION;
 (\<alpha>\<epsilon> e1) = (\<alpha>\<epsilon> e2);
 \<lbrakk>e1\<rbrakk>\<alpha>\<epsilon> = \<lbrakk>e2\<rbrakk>\<alpha>\<epsilon> \<rbrakk> \<Longrightarrow> e1 = e2"
apply (simp add: EvalAE_def)
apply (simp add: prod_eq_iff)
done

theorem EvalAE_closure [closure]:
"e \<in> WF_ALPHA_EXPRESSION \<Longrightarrow>
\<lbrakk>e\<rbrakk>\<alpha>\<epsilon> \<in> WF_EXPRESSION"
  by (simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def EvalAE_def)

theorem EvalAE_type [typing] :
"\<lbrakk>e \<in> WF_ALPHA_EXPRESSION; \<epsilon> e :e: t\<rbrakk> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<alpha>\<epsilon> :e: t"
  by (simp add:EvalAE_def)

theorem EvalAE_tau [simp]: 
"e \<in> WF_ALPHA_EXPRESSION \<Longrightarrow> \<tau>e \<lbrakk>e\<rbrakk>\<alpha>\<epsilon> = \<tau>e (\<epsilon> e)"
  by (simp add:EvalAE_def)

subsection {* Distribution Theorems *}

theorem EvalAE_VarAE [evala] :
"\<lbrakk>VarAE x\<rbrakk>\<alpha>\<epsilon> = VarE x"
  by (simp add:VarAE_def EvalAE_def)

theorem EvalA_EqualA [evala] :
"\<lbrakk>e1 \<in> WF_ALPHA_EXPRESSION; 
 e2 \<in> WF_ALPHA_EXPRESSION\<rbrakk> \<Longrightarrow>
\<lbrakk>e1 ==\<alpha> e2\<rbrakk>\<pi> = (\<lbrakk>e1\<rbrakk>\<alpha>\<epsilon> ==p \<lbrakk>e2\<rbrakk>\<alpha>\<epsilon>)"
  by (simp add:EqualA_def EvalA_def EvalAE_def)

theorem EvalE_LitAE [evala] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>LitAE t v\<rbrakk>\<alpha>\<epsilon> = LitE t v"
  by (simp add: LitAE_def EvalAE_def)

theorem EvalA_SubstA [evala] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 v \<in> WF_ALPHA_EXPRESSION\<rbrakk> \<Longrightarrow>
 \<lbrakk>SubstA p v x\<rbrakk>\<pi> = (\<exists>p {x} . \<lbrakk>p\<rbrakk>\<pi> \<and>p ((VarE x) ==p \<lbrakk>v\<rbrakk>\<alpha>\<epsilon>))"
  apply (simp add:SubstA_def)
  apply (utp_alpha_tac)
done


theorem EvalA_SubstAE [evala] :
"\<lbrakk>f \<in> WF_ALPHA_EXPRESSION;
 v \<in> WF_ALPHA_EXPRESSION\<rbrakk> \<Longrightarrow>
 \<lbrakk>SubstAE f v x\<rbrakk>\<alpha>\<epsilon> = SubstE \<lbrakk>f\<rbrakk>\<alpha>\<epsilon> \<lbrakk>v\<rbrakk>\<alpha>\<epsilon> x"
  by (simp add:SubstAE_def EvalAE_def)

subsection {* Proof Experiements *}

theorem SubstAE_VarAE:
"\<lbrakk>e \<in> WF_ALPHA_EXPRESSION; type x = \<tau>e (\<epsilon> e)\<rbrakk> \<Longrightarrow>
 SubstAE (VarAE x) e x = e"
  apply (subgoal_tac "\<epsilon> e :e: type x")
  apply (utp_alpha_tac)
  apply (utp_expr_tac)
  apply (simp add:typing)
done

end
end