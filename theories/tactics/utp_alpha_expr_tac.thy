(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_alpha_expr_tac.thy                                               *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Proof Tactic for Alphabetised Expressions *}

theory utp_alpha_expr_tac
imports "../alpha/utp_alpha_expr" utp_pred_tac utp_expr_tac utp_alpha_tac
begin

subsection {* Interpretation Function *}

definition EvalAE ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow>
   'VALUE WF_EXPRESSION" ("\<lbrakk>_\<rbrakk>\<alpha>\<epsilon>") where
"EvalAE e = \<epsilon> e"

subsection {* Transfer Theorems *}

theorem EvalAE_simp [evala] :
"e1 = e2 \<longleftrightarrow> (\<alpha> e1) = (\<alpha> e2) \<and> \<lbrakk>e1\<rbrakk>\<alpha>\<epsilon> = \<lbrakk>e2\<rbrakk>\<alpha>\<epsilon>"
  by (auto simp add: EvalAE_def)

theorem EvalAE_intro :
"\<lbrakk>\<alpha> e1 = \<alpha> e2;
 \<lbrakk>e1\<rbrakk>\<alpha>\<epsilon> = \<lbrakk>e2\<rbrakk>\<alpha>\<epsilon> \<rbrakk> \<Longrightarrow> e1 = e2"
  by (auto simp add: EvalAE_def)

theorem EvalAE_type [typing] :
"\<lbrakk>e :\<^sub>\<alpha> t\<rbrakk> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<alpha>\<epsilon> :\<^sub>e t"
  by (simp add:EvalAE_def eatype_rel_def)

theorem EvalAE_compat [typing] :
"\<lbrakk>e \<rhd>\<^sub>\<alpha> x\<rbrakk> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x"
  by (simp add: EvalAE_def eavar_compat_def)

(*
theorem EvalAE_tau: 
"\<tau>e (\<epsilon> e) = \<tau>e \<lbrakk>e\<rbrakk>\<alpha>\<epsilon>"
  by (simp add:EvalAE_def)
*)

theorem EvalAE_expr [evala]:
  "\<epsilon> e = \<lbrakk>e\<rbrakk>\<alpha>\<epsilon>"
  by (simp add:EvalAE_def)

theorem EvalAE_UNREST_EXPR [unrest] :
"UNREST_EXPR (VAR - \<langle>\<alpha> e\<rangle>\<^sub>f) \<lbrakk>e\<rbrakk>\<alpha>\<epsilon>"
  by (simp add: EvalAE_def unrest)


subsection {* Distribution Theorems *}

theorem EvalAE_VarAE [evala] :
"\<lbrakk>VarAE x\<rbrakk>\<alpha>\<epsilon> = VarE x"
  by (auto simp add:VarAE.rep_eq EvalAE_def)

theorem EvalAE_VarA [evala] :
"\<lbrakk>VarA x\<rbrakk>\<pi> = VarP x"
  by (auto simp add:VarA.rep_eq EvalA_def)

theorem EvalA_EqualA [evala] :
"\<lbrakk>e1 ==\<alpha> e2\<rbrakk>\<pi> = (\<lbrakk>e1\<rbrakk>\<alpha>\<epsilon> ==p \<lbrakk>e2\<rbrakk>\<alpha>\<epsilon>)"
  by (simp add:EqualA.rep_eq EvalA_def EvalAE_def)

theorem EvalE_LitAE [evala] :
"\<lbrakk>LitAE t v\<rbrakk>\<alpha>\<epsilon> = LitE t v"
  by (simp add: LitAE.rep_eq EvalAE_def)

theorem EvalE_TrueAE [evala] :
"\<lbrakk>TrueAE\<rbrakk>\<alpha>\<epsilon> = TrueE"
  by (simp add:TrueAE.rep_eq EvalAE_def)

theorem EvalE_FalseAE [evala] :
"\<lbrakk>FalseAE\<rbrakk>\<alpha>\<epsilon> = FalseE"
  by (simp add:FalseAE.rep_eq EvalAE_def)

theorem EvalA_ExprA [evala] :
"e :\<^sub>\<alpha> BoolType \<Longrightarrow> \<lbrakk>ExprA e\<rbrakk>\<pi> = ExprP \<lbrakk>e\<rbrakk>\<alpha>\<epsilon>"
  by (simp add:ExprA_rep_eq EvalA_def EvalAE_def)

theorem EvalA_RenameAE [evala] :
"\<lbrakk>e[ss]\<alpha>\<epsilon>\<rbrakk>\<alpha>\<epsilon> = \<lbrakk>e\<rbrakk>\<alpha>\<epsilon>[ss]\<epsilon>"
  by (simp add:RenameAE.rep_eq EvalAE_def)
 
theorem EvalA_SubstA :
"\<lbrakk> v \<rhd>\<^sub>\<alpha> x; x \<notin>\<^sub>f \<alpha> v \<rbrakk> \<Longrightarrow> \<lbrakk>SubstA p v x\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi>[\<lbrakk>v\<rbrakk>\<alpha>\<epsilon>|x]"
  by (simp add:SubstA_rep_eq EvalA_def EvalAE_def)

theorem EvalA_SubstAE [evala] :
"v \<rhd>\<^sub>\<alpha> x \<Longrightarrow> \<lbrakk>SubstAE f v x\<rbrakk>\<alpha>\<epsilon> = \<lbrakk>f\<rbrakk>\<alpha>\<epsilon>[\<lbrakk>v\<rbrakk>\<alpha>\<epsilon>|x]"
  by (simp add:SubstAE_rep_eq EvalAE_def)

theorem EvalA_is_SubstP_var [evala]:
  "\<exists> x'. is_SubstP_var \<lbrakk>p\<rbrakk>\<pi> \<lbrakk>v\<rbrakk>\<alpha>\<epsilon> x x'"
  by (simp add:EvalA_def WF_ALPHA_EXPRESSION_is_SubstP_var EvalAE_def)

theorem EvalP_EvalA_SubstA [evala]: 
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x; x \<notin>\<^sub>f \<alpha> v \<rbrakk> \<Longrightarrow> \<lbrakk>\<lbrakk>p[v|x]\<alpha>\<rbrakk>\<pi>\<rbrakk>b = \<lbrakk>\<lbrakk>p\<rbrakk>\<pi>\<rbrakk>(b(x :=\<^sub>b \<lbrakk>\<lbrakk>v\<rbrakk>\<alpha>\<epsilon>\<rbrakk>\<epsilon>b))"
  by (metis (full_types) EvalAE_expr EvalA_SubstA EvalA_def EvalE_SubstP WF_ALPHA_EXPRESSION_is_SubstP_var eavar_compat_def)

subsection {* Proof Experiements *}

(*
theorem SubstAE_VarAE:
"vtype x = \<tau>\<^sub>e (\<epsilon> e) \<Longrightarrow>
 SubstAE (VarAE x) e x = e"
  apply (subgoal_tac "\<epsilon> e :\<^sub>e vtype x")
  apply (utp_alpha_tac)
  apply (utp_expr_tac)
  apply (simp add:alphabet)
  apply (auto)
  apply (simp add:typing)
done
*)

subsubsection {* Simplifications *}

theorem ExprA_true [simp]: "ExprA TrueAE = TRUE"
  by (utp_alpha_tac2)

theorem ExprA_false [simp]: "ExprA FalseAE = FALSE"
  by (utp_alpha_tac2)

end