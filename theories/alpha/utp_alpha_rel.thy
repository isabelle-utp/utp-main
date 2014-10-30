(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_rel.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Relations *}

theory utp_alpha_rel
imports 
  utp_alpha_pred 
  utp_alpha_expr
  "../core/utp_pred"
  "../core/utp_rel"
  "../core/utp_iteration"
  "../laws/utp_rel_laws"
  "../tactics/utp_alpha_tac" 
  "../tactics/utp_alpha_expr_tac"
  "../tactics/utp_rel_tac"
begin

subsection {* Restrictions *}

definition WF_ALPHA_REL :: "'a uapred set" where
"WF_ALPHA_REL = {p . (\<alpha> p) \<in> REL_ALPHABET}"

definition HOM_RELATION :: "'a uapred set" where
"HOM_RELATION = {p . (\<alpha> p) \<in> HOM_ALPHABET \<and> (\<alpha> p) \<in> REL_ALPHABET}"

(*
definition WF_REL_EXPR :: "'VALUE WF_ALPHA_EXPRESSION set" where
"WF_REL_EXPR = {e . (\<alpha> e) \<in> REL_ALPHABET}"
*)

typedef 'a WF_ALPHA_REL = "WF_ALPHA_REL :: 'a uapred set"
  apply (auto simp add:WF_ALPHA_REL_def REL_ALPHABET_def)
  apply (metis TrueA_alphabet le_supI1 utp_alphabet.in_UNDASHED)
done

definition WF_ALPHA_COND :: "'a uapred set" where
"WF_ALPHA_COND = {p . p \<in> WF_ALPHA_REL \<and> UNREST DASHED (\<pi> p)}"

definition WF_ALPHA_POST :: "'a uapred set" where
"WF_ALPHA_POST = {p . p \<in> WF_ALPHA_REL \<and> UNREST D\<^sub>0 (\<pi> p)}"

adhoc_overloading
  REL WF_ALPHA_REL

adhoc_overloading
  COND WF_ALPHA_COND

adhoc_overloading
  POST WF_ALPHA_POST

subsection {* Operators *}

subsubsection {* Skip *}

lift_definition SkipA :: "'a alpha \<Rightarrow> 'a uapred" is
"\<lambda> a. (a, SkipRA \<langle>a\<rangle>\<^sub>f)"
  by (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)

notation SkipA ("II\<alpha>\<^bsub>_\<^esub>")

subsubsection {* Assignment *}

definition AssignA ::
"'a uvar \<Rightarrow>
 'a alpha \<Rightarrow>
 'a uaexpr \<Rightarrow>
 'a uapred" where
"a \<in> REL_ALPHABET \<Longrightarrow>
 AssignA x a v \<equiv> MkPredA (a, AssignRA x \<langle>a\<rangle>\<^sub>f (\<epsilon> v))"

notation AssignA ("_ :=\<^bsub>_ \<^esub>_" [190] 190)

subsubsection {* Conditional *}

text {* Should we impose a constraint on b for it to be a condition? *}

lift_definition CondA ::
  "'a uapred \<Rightarrow>
   'a uapred \<Rightarrow>
   'a uapred \<Rightarrow>
   'a uapred" 
is "\<lambda> r1 b r2. (\<alpha> r1 |\<union>| \<alpha> b |\<union>| \<alpha> r2, (\<pi> r1) \<lhd> (\<pi> b) \<rhd> (\<pi> r2))"
  by (auto intro: unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation CondA ("_ \<lhd> _ \<rhd>\<^sub>\<alpha> _")
subsubsection {* Sequential Composition *}

lift_definition SemiA ::
  "'a uapred \<Rightarrow>
   'a uapred \<Rightarrow>
   'a uapred"
is "\<lambda> p q. (in\<^sub>\<alpha> (\<alpha> p) |\<union>| out\<^sub>\<alpha> (\<alpha> q) |\<union>| nrel\<^sub>\<alpha> (\<alpha> p |\<union>| \<alpha> q), (\<pi> p) ;\<^sub>R (\<pi> q))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule UNREST_SemiR_general)
  apply (rule unrest)
  apply (rule unrest) 
  apply (simp add:var_dist)
  apply (auto simp add:var_defs)
done

notation SemiA (infixr ";\<^sub>\<alpha>" 140)

definition ConvA ::
"'a uapred \<Rightarrow>
 'a uapred" where
"ConvA p = SS\<bullet>p"

definition VarExtA ::
"'m uapred \<Rightarrow> 'm uvar \<Rightarrow> 'm uapred" ("_\<^bsub>+_\<^esub>") where
"VarExtA p x = p \<and>\<^sub>\<alpha> ($\<^sub>\<alpha>x\<acute> ==\<^sub>\<alpha> $\<^sub>\<alpha>x)"

definition VarOpenA :: "'m uvar \<Rightarrow> 'm alpha \<Rightarrow> 'm uapred" where
"VarOpenA x A = (\<exists>\<^sub>\<alpha> \<lbrace>x\<rbrace>. II\<alpha>\<^bsub>A\<^esub>)"

definition VarCloseA :: "'m uvar \<Rightarrow> 'm alpha \<Rightarrow> 'm uapred" where
"VarCloseA x A = (\<exists>\<^sub>\<alpha> \<lbrace>x\<acute>\<rbrace>. II\<alpha>\<^bsub>A\<^esub>)"

definition "VarDeclA x A p \<equiv> (VarOpenA x (finsert x (finsert x\<acute> A)) ;\<^sub>\<alpha> p ;\<^sub>\<alpha> VarCloseA x (finsert x (finsert x\<acute> A)))"

adhoc_overloading
  prime ConvA

(*
lift_definition CoercePreA :: "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^sub>\<leftarrow>")
is "\<lambda> (a, P). (a, \<exists>\<^sub>p D\<^sub>1. P)"

lift_definition CoercePostA :: "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^sub>\<rightarrow>")
is "\<lambda> (a, P). (a, \<exists>\<^sub>p D\<^sub>0. P)"
*)

subsection {* Theorems *}

theorem WF_ALPHA_REL_unfold :
"r \<in> WF_ALPHA_REL \<longleftrightarrow>
 \<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
  by (simp add: WF_ALPHA_REL_def REL_ALPHABET_def)

(*
theorem WF_ALPHA_COND_unfold :
"r \<in> WF_ALPHA_COND \<longleftrightarrow>
 \<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> UNDASHED"
apply (simp add: WF_ALPHA_COND_def WF_ALPHA_REL_def REL_ALPHABET_def)
apply (insert WF_ALPHA_PREDICATE_UNREST[of r])
apply (auto)
done
*)


lemma WF_ALPHA_REL_EvalA_WF_RELATION [closure]:
  "P \<in> WF_ALPHA_REL \<Longrightarrow> \<lbrakk>P\<rbrakk>\<pi> \<in> WF_RELATION"
  apply (simp add:WF_ALPHA_REL_def WF_RELATION_def REL_ALPHABET_def)
  apply (rule UNREST_subset)
  apply (rule UNREST_EvalA)
  apply (auto)
done

lemma WF_ALPHA_COND_EvalA_WF_CONDITION [closure]:
  "p \<in> WF_ALPHA_COND \<Longrightarrow> \<lbrakk>p\<rbrakk>\<pi> \<in> WF_CONDITION"
  apply (auto simp add:WF_ALPHA_COND_def WF_CONDITION_def)
  apply (simp add:closure)
  apply (simp add:EvalA_def)
done

lemma WF_ALPHA_POST_EvalA_WF_POSTCOND [closure]:
  "p \<in> POST \<Longrightarrow> \<lbrakk>p\<rbrakk>\<pi> \<in> POST"
  apply (auto simp add:WF_ALPHA_POST_def WF_POSTCOND_def)
  apply (simp add:closure)
  apply (simp add:EvalA_def)
done

lemma WF_RELATION_REL_ALPHABET [closure]: 
  "\<alpha> P \<in> REL_ALPHABET \<Longrightarrow> \<lbrakk>P\<rbrakk>\<pi> \<in> WF_RELATION"
  by (auto intro:closure simp add:WF_ALPHA_REL_def)

(*
lemma WF_ALPHA_REL_REL_ALPHABET [closure]:
  "\<alpha> P \<in> REL_ALPHABET \<Longrightarrow> P \<in> WF_ALPHA_REL"
  by (simp add:WF_ALPHA_REL_def)
*)

lemma HOMOGENEOUS_HOM_ALPHA [closure]:
  "a \<in> HOM_ALPHABET \<Longrightarrow> HOMOGENEOUS \<langle>a\<rangle>\<^sub>f"
  by (metis (mono_tags) HOM_ALPHABET_def HOM_ALPHA_HOMOGENEOUS mem_Collect_eq)

theorem WF_ALPHA_REL_intro [intro] :
  "\<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow>
   r \<in> WF_ALPHA_REL"
  by (simp add:WF_ALPHA_REL_unfold assms)

theorem WF_ALPHA_COND_WF_ALPHA_REL [closure] :
"r \<in> WF_ALPHA_COND \<Longrightarrow> r \<in> WF_ALPHA_REL"
  by (simp add: WF_ALPHA_COND_def)

theorem WF_ALPHA_POST_WF_ALPHA_REL [closure] :
"r \<in> WF_ALPHA_POST \<Longrightarrow> r \<in> WF_ALPHA_REL"
  by (simp add: WF_ALPHA_POST_def)

theorem HOM_RELATION_WF_ALPHA_REL [closure] :
"r \<in> HOM_RELATION \<Longrightarrow> r \<in> WF_ALPHA_REL"
  by (simp add:HOM_RELATION_def WF_ALPHA_REL_def HOM_ALPHABET_def)

theorem HOM_RELATION_HOM_ALPHABET [closure] :
"r \<in> HOM_RELATION \<Longrightarrow> (\<alpha> r) \<in> HOM_ALPHABET"
  by (simp add:HOM_RELATION_def HOM_ALPHABET_def)

(*
theorem WF_ALPHA_REL_REL_ALPHABET [closure] :
"r \<in> WF_ALPHA_REL \<Longrightarrow> (\<alpha> r) \<in> REL_ALPHABET"
  by (simp add: WF_ALPHA_REL_def)
*)

theorem REL_ALPHABET_UNDASHED_DASHED [closure]:
"a \<in> REL_ALPHABET \<Longrightarrow> \<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
  by (simp add: REL_ALPHABET_def)

lemma NON_REL_VAR_REL_ALPHABET [closure]: 
  "a \<in> REL_ALPHABET \<Longrightarrow> NON_REL_VAR \<subseteq> - \<langle>a\<rangle>\<^sub>f"
  apply (simp only: REL_ALPHABET_def NON_REL_VAR_def)
  apply (auto)
done

lemma REL_ALPHABET_WF_ALPHA_COND [closure]: 
  "p \<in> WF_ALPHA_COND \<Longrightarrow> \<alpha>(p) \<in> REL_ALPHABET"
  by (metis WF_ALPHA_COND_WF_ALPHA_REL WF_ALPHA_REL_def mem_Collect_eq)

lemma REL_ALPHABET_WF_ALPHA_POST [closure]: 
  "p \<in> WF_ALPHA_POST \<Longrightarrow> \<alpha>(p) \<in> REL_ALPHABET"
  by (metis WF_ALPHA_POST_WF_ALPHA_REL WF_ALPHA_REL_def mem_Collect_eq)

lemma REL_ALPHABET_WF_ALPHA_REL [closure]: 
  "p \<in> WF_ALPHA_REL \<Longrightarrow> \<alpha>(p) \<in> REL_ALPHABET"
  by (metis WF_ALPHA_COND_WF_ALPHA_REL WF_ALPHA_REL_def mem_Collect_eq)

theorem WF_ALPHA_REL_UNREST_UNDASHED [unrest]:
  "r \<in> WF_ALPHA_REL \<Longrightarrow> UNREST DASHED_TWICE (\<pi> r)"
  apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def)
  apply (rule_tac ?vs1.0="- \<langle>\<alpha> r\<rangle>\<^sub>f" in UNREST_subset)
  apply (auto intro:unrest)
done

lemma HOM_ALPHABET_dash_in [simp]:
  "a \<in> HOM_ALPHABET \<Longrightarrow> dash ` in \<langle>a\<rangle>\<^sub>f = out \<langle>a\<rangle>\<^sub>f"
  by (metis HOMOGENEOUS_HOM_ALPHA HOMOGENEOUS_dash_in)

lemma HOM_ALPHABET_undash_out [simp]: 
  "a \<in> HOM_ALPHABET \<Longrightarrow> undash ` out \<langle>a\<rangle>\<^sub>f = in \<langle>a\<rangle>\<^sub>f"
  by (metis HOM_ALPHABET_dash_in undash_dash_image)

subsubsection {* Closure Theorems *}

text {* TODO: Provide a complete set of closure theorems! *}

theorem REL_ALPHABET_empty [closure]:
  "\<lbrace>\<rbrace> \<in> REL_ALPHABET"
  by (simp add:REL_ALPHABET_def)

theorem REL_ALPHABET_finsert [closure]:
  "\<lbrakk> x \<in> UNDASHED \<union> DASHED; a \<in> REL_ALPHABET \<rbrakk> \<Longrightarrow> finsert x a \<in> REL_ALPHABET"
  by (simp add:REL_ALPHABET_def)

theorem REL_ALPHABET_union [closure]:
  "\<lbrakk> a1 \<in> REL_ALPHABET; a2 \<in> REL_ALPHABET \<rbrakk> \<Longrightarrow> (a1 |\<union>| a2) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def)

theorem REL_ALPHABET_inter [closure]:
  "\<lbrakk> a1 \<in> REL_ALPHABET; a2 \<in> REL_ALPHABET \<rbrakk> \<Longrightarrow> (a1 |\<inter>| a2) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def)

theorem REL_ALPHABET_minus [closure]:
  "a1 \<in> REL_ALPHABET \<Longrightarrow> (a1 -\<^sub>f a2) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def)

theorem HOM_ALPHABET_empty [closure]:
  "\<lbrace>\<rbrace> \<in> HOM_ALPHABET"
  by (simp add:HOM_ALPHABET_def HOM_ALPHA_unfold)

theorem HOM_ALPHABET_union [closure]:
  "\<lbrakk> a1 \<in> HOM_ALPHABET; a2 \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> (a1 |\<union>| a2) \<in> HOM_ALPHABET"
  by (auto simp add:HOM_ALPHABET_def HOM_ALPHA_unfold alphabet_dist)

theorem HOM_ALPHABET_inter [closure]:
  "\<lbrakk> a1 \<in> HOM_ALPHABET; a2 \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> (a1 |\<inter>| a2) \<in> HOM_ALPHABET"
  by (auto simp add:HOM_ALPHABET_def HOM_ALPHA_unfold alphabet_dist)

theorem HOM_ALPHABET_minus [closure]:
  "\<lbrakk> a1 \<in> HOM_ALPHABET; a2 \<in> HOM_ALPHABET \<rbrakk> \<Longrightarrow> (a1 -\<^sub>f a2) \<in> HOM_ALPHABET"
  by (auto simp add:HOM_ALPHABET_def HOM_ALPHA_unfold alphabet_dist)

theorem HOM_ALPHABET_hom_right [closure]: 
  "homr\<^sub>\<alpha> a \<in> HOM_ALPHABET"
  by (auto intro!:fset_intro simp add:HOM_ALPHABET_def HOM_ALPHA_unfold homr_alpha.rep_eq alphabet_dist fimage.rep_eq)
  
  
theorem HOM_ALPHABET_hom_left [closure]: 
  "homl\<^sub>\<alpha> a \<in> HOM_ALPHABET"
  by (auto intro!:fset_intro simp add:HOM_ALPHABET_def HOM_ALPHA_unfold homl_alpha.rep_eq alphabet_dist fimage.rep_eq)

theorem NotA_WF_ALPHA_REL [closure] :
"\<lbrakk>r \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 \<not>\<^sub>\<alpha> r \<in> WF_ALPHA_REL"
  by (simp add: WF_ALPHA_REL_unfold alphabet)

theorem NotA_WF_ALPHA_COND [closure] :
"\<lbrakk>r \<in> WF_ALPHA_COND\<rbrakk> \<Longrightarrow>
 \<not>\<^sub>\<alpha> r \<in> WF_ALPHA_COND"
apply (simp add:WF_ALPHA_COND_def)
apply (simp add:closure)
apply (simp add:NotA.rep_eq)
apply (auto intro: unrest)
done

theorem NotA_WF_ALPHA_POST [closure] :
"r \<in> POST \<Longrightarrow> \<not>\<^sub>\<alpha> r \<in> POST"
  by (metis (lifting, no_types) EvalA_NotA EvalA_def NotA_WF_ALPHA_REL UNREST_NotP WF_ALPHA_POST_def mem_Collect_eq)

theorem AndA_WF_ALPHA_REL [closure] :
"\<lbrakk>r1 \<in> WF_ALPHA_REL;
 r2 \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 r1 \<and>\<^sub>\<alpha> r2 \<in> WF_ALPHA_REL"
  by (simp add: WF_ALPHA_REL_unfold alphabet)

theorem AndA_WF_ALPHA_COND [closure] :
"\<lbrakk>r1 \<in> WF_ALPHA_COND;
 r2 \<in> WF_ALPHA_COND\<rbrakk> \<Longrightarrow>
 r1 \<and>\<^sub>\<alpha> r2 \<in> WF_ALPHA_COND"
apply (simp add:WF_ALPHA_COND_def)
apply (simp add:AndA.rep_eq closure)
apply (auto intro:unrest)
done

theorem AndA_WF_ALPHA_POST [closure] :
"\<lbrakk>r1 \<in> WF_ALPHA_POST;
 r2 \<in> WF_ALPHA_POST\<rbrakk> \<Longrightarrow>
 r1 \<and>\<^sub>\<alpha> r2 \<in> WF_ALPHA_POST"
apply (simp add:WF_ALPHA_POST_def)
apply (simp add:AndA.rep_eq closure)
apply (auto intro:unrest)
done

theorem OrA_WF_ALPHA_REL [closure] :
"\<lbrakk>r1 \<in> WF_ALPHA_REL;
 r2 \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 r1 \<or>\<^sub>\<alpha> r2 \<in> WF_ALPHA_REL"
  by (simp add: WF_ALPHA_REL_unfold alphabet)

theorem OrA_WF_ALPHA_COND [closure] :
"\<lbrakk>r1 \<in> WF_ALPHA_COND;
 r2 \<in> WF_ALPHA_COND\<rbrakk> \<Longrightarrow>
 r1 \<or>\<^sub>\<alpha> r2 \<in> WF_ALPHA_COND"
apply (simp add:WF_ALPHA_COND_def)
apply (simp add:OrA.rep_eq closure)
apply (auto intro:unrest)
done

theorem ImpliesA_WF_ALPHA_REL [closure] :
"\<lbrakk>r1 \<in> WF_ALPHA_REL;
 r2 \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 r1 \<Rightarrow>\<^sub>\<alpha> r2 \<in> WF_ALPHA_REL"
  by (simp add: WF_ALPHA_REL_unfold alphabet)

theorem ImpliesA_WF_ALPHA_COND [closure] :
"\<lbrakk>r1 \<in> WF_ALPHA_COND;
 r2 \<in> WF_ALPHA_COND\<rbrakk> \<Longrightarrow>
 r1 \<Rightarrow>\<^sub>\<alpha> r2 \<in> WF_ALPHA_COND"
apply (simp add:WF_ALPHA_COND_def)
apply (simp add:ImpliesA.rep_eq closure)
apply (auto intro:unrest)
done

theorem TrueA_WF_ALPHA_REL [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 true\<^bsub>a\<^esub> \<in> WF_ALPHA_REL"
apply (simp add:WF_ALPHA_REL_def)
apply (simp add:closure alphabet)
done

theorem TrueA_WF_ALPHA_COND [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 true\<^bsub>a\<^esub> \<in> WF_ALPHA_COND"
apply (simp add:WF_ALPHA_COND_def)
apply (simp add:TrueA.rep_eq closure)
apply (auto intro:unrest)
done

theorem FalseA_WF_ALPHA_REL [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 false\<^bsub>a\<^esub> \<in> WF_ALPHA_REL"
apply (simp add:WF_ALPHA_REL_def)
apply (simp add:closure alphabet)
done

theorem FalseA_WF_ALPHA_COND [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 false\<^bsub>a\<^esub> \<in> WF_ALPHA_COND"
apply (simp add:WF_ALPHA_COND_def)
apply (simp add:FalseA.rep_eq closure)
apply (auto intro:unrest)
done

theorem ExtA_WF_ALPHA_REL [closure] :
"\<lbrakk> a \<in> REL_ALPHABET; p \<in> WF_ALPHA_REL \<rbrakk> \<Longrightarrow>
 p \<oplus>\<^sub>\<alpha> a \<in> WF_ALPHA_REL"
  by (auto intro:closure simp add:ExtA.rep_eq WF_ALPHA_REL_def alphabet)

theorem ExtA_WF_ALPHA_COND [closure] :
"\<lbrakk> \<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED; p \<in> WF_ALPHA_COND \<rbrakk> \<Longrightarrow>
 p \<oplus>\<^sub>\<alpha> a \<in> WF_ALPHA_COND"
  apply (auto intro:closure simp add:ExtA.rep_eq WF_ALPHA_COND_def alphabet)
  apply (rule closure)
  apply (force simp add:REL_ALPHABET_def)
  apply (simp)
done

theorem ExistsResA_WF_ALPHA_REL [closure]:
"p \<in> WF_ALPHA_REL \<Longrightarrow>
 (\<exists>-\<^sub>\<alpha> a. p) \<in> WF_ALPHA_REL"
  by (auto intro:closure simp add:WF_ALPHA_REL_def alphabet)

theorem ExistsResA_WF_ALPHA_COND [closure]:
"p \<in> WF_ALPHA_COND \<Longrightarrow>
 (\<exists>-\<^sub>\<alpha> a. p) \<in> WF_ALPHA_COND"
  by (auto intro:closure unrest simp add:WF_ALPHA_COND_def alphabet ExistsResA.rep_eq)

theorem ExistsA_WF_ALPHA_REL [closure]:
"p \<in> WF_ALPHA_REL \<Longrightarrow>
 (\<exists>\<^sub>\<alpha> a. p) \<in> WF_ALPHA_REL"
  by (auto intro:closure simp add:WF_ALPHA_REL_def alphabet)

theorem ExistsA_WF_ALPHA_COND [closure]:
"p \<in> WF_ALPHA_COND \<Longrightarrow>
 (\<exists>\<^sub>\<alpha> a. p) \<in> WF_ALPHA_COND"
  by (auto intro:closure unrest simp add:WF_ALPHA_COND_def alphabet ExistsA.rep_eq)

theorem EqualA_WF_ALPHA_REL [closure]:
"\<lbrakk> e \<in> REL; f \<in> REL \<rbrakk> \<Longrightarrow> e ==\<^sub>\<alpha> f \<in> REL"
  by (auto intro:closure simp add:WF_ALPHA_REL_def WF_ALPHA_EXPR_REL_def alphabet)

theorem EqualA_WF_ALPHA_COND [closure]:
"\<lbrakk> e \<in> COND; f \<in> COND \<rbrakk> \<Longrightarrow> e ==\<^sub>\<alpha> f \<in> COND"
  apply (simp add:WF_ALPHA_EXPR_COND_def WF_ALPHA_COND_def)
  apply (simp add:closure)
  apply (metis EvalAE_expr EvalA_EqualA EvalA_def UNREST_EqualP)
done

theorem VarAE_WF_REL_EXPR [closure]:
"x \<in> UNDASHED \<union> DASHED \<Longrightarrow>
 VarAE x \<in> WF_ALPHA_EXPR_REL"
  by (auto intro:closure simp add:WF_ALPHA_EXPR_REL_def alphabet)

theorem LitAE_WF_REL_EXPR [closure]:
"LitAE v \<in> WF_ALPHA_EXPR_REL"
  by (simp add:WF_ALPHA_EXPR_REL_def alphabet closure)

theorem SkipA_closure [closure] :
"a \<in> REL_ALPHABET \<Longrightarrow>
 II\<alpha>\<^bsub>a\<^esub> \<in> WF_ALPHA_REL"
  by (simp add: WF_ALPHA_REL_def REL_ALPHABET_def pred_alphabet_def SkipA.rep_eq)

lemma SkipRA_closure' [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow> II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub> \<in> WF_RELATION"
  by (metis UNREST_SkipRA_NON_REL_VAR WF_RELATION_UNREST)

theorem AssignA_rep_eq:
  "\<lbrakk> a \<in> REL_ALPHABET
   ; x |\<in>| a; dash x |\<in>| a
   ; \<alpha> v |\<subseteq>| a \<rbrakk> \<Longrightarrow> 
   \<langle>x :=\<^bsub>a\<^esub> v\<rangle>\<^sub>\<alpha> = (a, AssignRA x \<langle>a\<rangle>\<^sub>f (\<epsilon> v))"
  apply (subgoal_tac "x \<in> UNDASHED")
  apply (subgoal_tac "(a, x :=\<^bsub>\<langle>a\<rangle>\<^sub>f \<^esub>\<epsilon> v) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:AssignA_def)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (subgoal_tac "UNREST (- ({dash x} \<union> \<langle>a\<rangle>\<^sub>f)) (x :=\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub>\<epsilon> v)")
  apply (subgoal_tac "\<langle>a\<rangle>\<^sub>f = {dash x} \<union> (\<langle>a\<rangle>\<^sub>f - {dash x})")
  apply (force)
  apply (metis Un_Diff_cancel Un_commute Un_insert_right fnmember_intro insert_absorb sup_bot.right_neutral)
  apply (rule unrest)
  apply (simp)
  apply (rule UNREST_EXPR_subset)
  apply (rule unrest)
  apply (auto simp add:REL_ALPHABET_def intro:typing)
  apply (metis DASHED_dash_elim UNDASHED_dash_DASHED Un_iff dashed_twice_contras(2) fnmember_intro insert_absorb insert_subset)
done

theorem AssignA_closure [closure] :
  assumes 
   "a \<in> REL_ALPHABET"
   "x |\<in>| a" "dash x |\<in>| a"
   "\<alpha> v |\<subseteq>| a"
  shows "x :=\<^bsub>a\<^esub> v \<in> WF_ALPHA_REL"
proof
  from assms show "\<langle>\<alpha> (x :=\<^bsub>a \<^esub>v)\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
    apply (simp add:AssignA_rep_eq pred_alphabet_def)
    apply (simp add:REL_ALPHABET_def)
  done
qed

theorem RenameA_SS_closure [closure]:
  "p \<in> WF_ALPHA_REL \<Longrightarrow> SS\<bullet>p \<in> WF_ALPHA_REL"
  apply (auto simp add:WF_ALPHA_REL_def REL_ALPHABET_def alphabet)
  apply (metis (lifting) SS_VAR_RENAME_INV SS_ident_app UnE VAR_RENAME_INV_app set_rev_mp)
done

theorem CondA_closure [closure] :
  assumes "r1 \<in> WF_ALPHA_REL" "r2 \<in> WF_ALPHA_REL"
    "b \<in> WF_ALPHA_COND" "(\<alpha> r1) = (\<alpha> r2)" "(\<alpha> b) |\<subseteq>| (\<alpha> r1)"
 shows "(r1 \<lhd> b \<rhd>\<^sub>\<alpha> r2) \<in> WF_ALPHA_REL"
proof 
  from assms show "\<langle>\<alpha> r1 \<lhd> b \<rhd>\<^sub>\<alpha> r2\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED"
    by (auto simp add: CondA.rep_eq pred_alphabet_def WF_ALPHA_REL_def REL_ALPHABET_def)
qed

(*
theorem SemiA_rep_eq:
"\<lbrakk>r1 \<in> WF_ALPHA_REL;
 r2 \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 DestPredA (r1 ;\<^sub>\<alpha> r2) = (in\<^sub>\<alpha> (\<alpha> r1) |\<union>| out\<^sub>\<alpha> (\<alpha> r2), (\<pi> r1) ; (\<pi> r2))"
  apply (subgoal_tac "(in\<^sub>\<alpha> (\<alpha> r1) |\<union>| out\<^sub>\<alpha> (\<alpha> r2), (\<pi> r1) ; (\<pi> r2)) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:SemiA_def)
  apply (frule WF_ALPHA_REL_UNREST_UNDASHED)
  apply (frule WF_ALPHA_REL_UNREST_UNDASHED) back
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule UNREST_SemiR)
  apply (auto)
  apply (metis (hide_lams, no_types) Un_iff WF_ALPHA_REL_unfold set_mp)+
done
*)

theorem SemiA_closure [closure] :
  assumes "r1 \<in> WF_ALPHA_REL" "r2 \<in> WF_ALPHA_REL"
  shows "r1 ;\<^sub>\<alpha> r2 \<in> WF_ALPHA_REL"
using assms
apply (simp add: WF_ALPHA_REL_unfold pred_alphabet_def)
apply (auto simp add:SemiA.rep_eq var_defs pred_alphabet_def)
done

subsection {* Alphabet Theorems *}

declare pred_alphabet_def [simp]

theorem SkipA_alphabet [alphabet] :
"\<alpha> (II\<alpha>\<^bsub>a\<^esub>) = a"
  by (simp add: SkipA.rep_eq)

theorem AssignA_alphabet [alphabet] :
"\<lbrakk> a \<in> REL_ALPHABET; a \<in> HOM_ALPHABET; x |\<in>| in\<^sub>\<alpha>(a); \<alpha> v |\<subseteq>| a \<rbrakk> \<Longrightarrow>
 \<alpha> (x :=\<^bsub>a\<^esub> v) = a"
  apply (simp add:pred_alphabet_def)
  apply (subst AssignA_rep_eq)
  apply (auto simp add:fmember_def fsubset_eq)
  apply (metis Int_iff in_vars_def)
  apply (metis (mono_tags) Diff_iff HOMOGENEOUS_HOM_ALPHA UNDASHED_minus_in hom_alphabet_undash set_mp utp_var.in_UNDASHED)
done

theorem CondA_alphabet [alphabet] :
"\<alpha> (r1 \<lhd> b \<rhd>\<^sub>\<alpha> r2) = (\<alpha> r1 |\<union>| \<alpha> b |\<union>| \<alpha> r2)"
  by (simp add: CondA.rep_eq)

lemma REL_ALPHABET_nrel_alpha [simp]:
  "a \<in> REL_ALPHABET \<Longrightarrow> nrel\<^sub>\<alpha> a = \<lbrace>\<rbrace>"
  by (auto simp add:fmember_def fsubset_eq REL_ALPHABET_def var_defs)

lemma WF_ALPHA_REL_nrel_alpha [simp]:
  "p \<in> WF_ALPHA_REL \<Longrightarrow> nrel\<^sub>\<alpha> (\<alpha> p) = \<lbrace>\<rbrace>"
  by (auto simp add:WF_ALPHA_REL_def REL_ALPHABET_def var_defs)

theorem SemiA_alphabet [alphabet] :
  "\<alpha> (p ;\<^sub>\<alpha> q) = in\<^sub>\<alpha> (\<alpha> p) |\<union>| out\<^sub>\<alpha> (\<alpha> q) |\<union>| nrel\<^sub>\<alpha> (\<alpha> p) |\<union>| nrel\<^sub>\<alpha> (\<alpha> q)"
  by (force simp add: fmember_def fsubset_eq SemiA.rep_eq WF_ALPHA_REL_def REL_ALPHABET_def var_defs)

theorem ConvA_alphabet [alphabet] :
  "\<alpha> (P\<acute>) = \<langle>SS\<rangle>\<^sub>s |`| \<alpha>(P :: 'a uapred)"
  by (metis ConvA_def PermA_alphabet)

lemma VarExtA_alphabet: "\<alpha>(P\<^bsub>+x\<^esub>) = finsert x (finsert x\<acute> (\<alpha>(P)))"
  by (simp add: VarExtA_def alphabet del: pred_alphabet_def)

subsection {* Evaluation Theorems *}

theorem EvalP_SkipP_override :
"vs \<subseteq> NON_REL_VAR \<Longrightarrow>
 \<lbrakk>II\<rbrakk>(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>II\<rbrakk>b1"
apply (simp add: SkipR_def)
apply (simp add: EvalP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "v" in bspec)
apply (assumption)
apply (subgoal_tac "v \<notin> vs", simp)
apply (subgoal_tac "dash v \<notin> vs", simp)
apply (metis DASHED_not_NON_REL_VAR UNDASHED_dash_DASHED set_mp)
apply (metis UNDASHED_not_NON_REL_VAR set_rev_mp)
-- {* Subgoal 3 *}
apply (subgoal_tac "v \<notin> vs", simp)
apply (subgoal_tac "dash v \<notin> vs", simp)
apply (metis DASHED_not_NON_REL_VAR UNDASHED_dash_DASHED set_rev_mp)
apply (metis UNDASHED_not_NON_REL_VAR set_rev_mp)
done

theorem EvalA_UNREST_DASHED_TWICE [unrest]:
  "r \<in> WF_ALPHA_REL \<Longrightarrow> UNREST DASHED_TWICE \<lbrakk>r\<rbrakk>\<pi>"
  by (simp add:EvalA_def unrest)

theorem WF_ALPHA_REL_UNREST_NON_REL_VAR [unrest]:
  "r \<in> WF_ALPHA_REL \<Longrightarrow> UNREST NON_REL_VAR (\<pi> r)"
  apply (rule UNREST_subset)
  apply (rule unrest) back
  apply (metis NON_REL_VAR_REL_ALPHABET REL_ALPHABET_WF_ALPHA_REL)
done

theorem EvalA_UNREST_out [unrest]:
  "p \<in> WF_ALPHA_REL \<Longrightarrow> UNREST (DASHED - out \<langle>\<alpha> p\<rangle>\<^sub>f) \<lbrakk>p\<rbrakk>\<pi>"
  by (auto intro:unrest UNREST_subset simp add:var_defs)

theorem EvalA_UNREST_in [unrest]:
  "p \<in> WF_ALPHA_REL \<Longrightarrow> UNREST (UNDASHED - in \<langle>\<alpha> p\<rangle>\<^sub>f) \<lbrakk>p\<rbrakk>\<pi>"
  by (auto intro:unrest UNREST_subset simp add:var_defs)

theorem EvalA_SkipA [evala] :
"\<lbrakk>II\<alpha>\<^bsub>a\<^esub>\<rbrakk>\<pi> = II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub>"
  by (simp add:EvalA_def SkipA.rep_eq)

theorem EvalA_CondA [evala] :
"\<lbrakk>r1 \<lhd> b \<rhd>\<^sub>\<alpha> r2\<rbrakk>\<pi> = \<lbrakk>r1\<rbrakk>\<pi> \<lhd> \<lbrakk>b\<rbrakk>\<pi> \<rhd> \<lbrakk>r2\<rbrakk>\<pi>"
  by (simp add: EvalA_def CondA.rep_eq)

theorem EvalA_SemiA [evala] :
"\<lbrakk>r1 ;\<^sub>\<alpha> r2\<rbrakk>\<pi> = \<lbrakk>r1\<rbrakk>\<pi> ;\<^sub>R \<lbrakk>r2\<rbrakk>\<pi>"
  by (simp add: EvalA_def SemiA.rep_eq)

theorem EvalA_AssignA [evala] :
"\<lbrakk> a \<in> REL_ALPHABET; a \<in> HOM_ALPHABET; x |\<in>| in\<^sub>\<alpha>(a); \<alpha> v |\<subseteq>| a \<rbrakk> \<Longrightarrow>
 \<lbrakk>x :=\<^bsub>a\<^esub> v\<rbrakk>\<pi> = x :=\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub> \<lbrakk>v\<rbrakk>\<epsilon>"
  apply (simp add:AssignA_rep_eq EvalA_def EvalAE_def)
  apply (subst AssignA_rep_eq)
  apply (simp_all add: fmember_def fsubset_eq)
  apply (metis Int_iff in_vars_def)
  apply (metis (mono_tags) Diff_iff HOMOGENEOUS_HOM_ALPHA UNDASHED_minus_in hom_alphabet_undash set_mp utp_var.in_UNDASHED)
done

theorem EvalA_ConvA [evala] :
  "\<lbrakk>P\<acute>\<rbrakk>\<pi> = \<lbrakk>P\<rbrakk>\<pi>\<acute>"
  by (metis ConvA_def ConvR_def EvalA_RenameA)

declare pred_alphabet_def [simp del]

subsubsection {* Proof Experiments *}

theorem SemiA_assoc :
"\<lbrakk>r1 \<in> WF_ALPHA_REL;
 r2 \<in> WF_ALPHA_REL;
 r3 \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 (r1 ;\<^sub>\<alpha> r2) ;\<^sub>\<alpha> r3 = r1 ;\<^sub>\<alpha> (r2 ;\<^sub>\<alpha> r3)"
apply (utp_alpha_tac)
apply (utp_rel_tac)
apply (auto simp add:var_dist)
done

theorem SemiA_OrA_distl :
"\<lbrakk>r1 \<in> WF_ALPHA_REL;
 r2 \<in> WF_ALPHA_REL;
 r3 \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 r1 ;\<^sub>\<alpha> (r2 \<or>\<^sub>\<alpha> r3) = (r1 ;\<^sub>\<alpha> r2) \<or>\<^sub>\<alpha> (r1 ;\<^sub>\<alpha> r3)"
apply (utp_alpha_tac)
apply (utp_rel_auto_tac)
done

theorem SemiA_OrA_distr :
"\<lbrakk>r1 \<in> WF_ALPHA_REL;
 r2 \<in> WF_ALPHA_REL;
 r3 \<in> WF_ALPHA_REL\<rbrakk> \<Longrightarrow>
 (r1 \<or>\<^sub>\<alpha> r2) ;\<^sub>\<alpha> r3 = (r1 ;\<^sub>\<alpha> r3) \<or>\<^sub>\<alpha> (r2 ;\<^sub>\<alpha> r3)"
apply (utp_alpha_tac)
apply (utp_rel_auto_tac)
done

theorem SemiA_SkipA_left:
  assumes 
    "a \<in> HOM_ALPHABET" "a \<in> REL_ALPHABET"
    "out\<^sub>\<alpha> a = (in\<alpha>(P))\<acute>"
  shows "II\<alpha>\<^bsub>a\<^esub> ;\<^sub>\<alpha> P = P"
proof -

  from assms have ina:"in\<^sub>\<alpha> a = in\<alpha>(P)"
    apply (simp add:HOM_ALPHABET_def HOM_ALPHA_HOMOGENEOUS dash_alpha_def)
    apply (erule fset_elim)
    apply (rule fset_intro)
    apply (clarsimp)
    apply (unfold HOMOGENEOUS_dash_in[THEN sym])
    apply (simp only: inj_on_Un_image_eq_iff[of dash, OF dash_inj])
  done

  moreover with assms have "II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub> ;\<^sub>R \<lbrakk>P\<rbrakk>\<pi> = \<lbrakk>P\<rbrakk>\<pi>"
    apply (rule_tac SemiR_SkipRA_left)
    apply (metis COMPOSABLE_def HOMOGENEOUS_def HOM_ALPHABET_dash_in)
    apply (rule UNREST_subset)
    apply (rule UNREST_EvalA)
    apply (metis (lifting, no_types) ComplI Diff_iff in_alphabet.rep_eq in_member subsetI)
  done

  ultimately show ?thesis using assms
    apply (utp_alpha_tac)
    apply (metis alphabet_split inf_sup_aci(6))
  done
qed

theorem SemiA_SkipA_right:
  assumes 
    "a \<in> HOM_ALPHABET" "a \<in> REL_ALPHABET"
    "in\<^sub>\<alpha> a = (out\<alpha>(P))\<acute>"
  shows "P ;\<^sub>\<alpha> II\<alpha>\<^bsub>a\<^esub> = P"
proof -
  from assms have outa:"out\<^sub>\<alpha> a = out\<alpha>(P)"
    apply (auto elim!:fset_elim intro!:fset_intro simp add:WF_ALPHA_REL_def HOM_ALPHABET_def HOMOGENEOUS_def COMPOSABLE_def REL_ALPHABET_def HOM_ALPHA_unfold dash_alpha_def)
    apply (metis Int_iff UNDASHED_dash_DASHED dashed_twice_contras(2) image_iff in_vars_def)
    apply (metis imageI utp_var.not_dash_member_in)
  done
    
  moreover with assms have "\<lbrakk>P\<rbrakk>\<pi> ;\<^sub>R II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub> = \<lbrakk>P\<rbrakk>\<pi>"
    apply (rule_tac SemiR_SkipRA_right)
    apply (metis COMPOSABLE_def HOMOGENEOUS_def HOM_ALPHABET_dash_in)
    apply (rule UNREST_subset)
    apply (rule UNREST_EvalA)
    apply (metis (lifting, no_types) ComplI Diff_iff out_alphabet.rep_eq out_member subsetI)
  done

  ultimately show ?thesis using assms
    apply (utp_alpha_tac)
    apply (metis alphabet_split inf_sup_aci(6))
  done
qed

theorem ClosureA_rel_closure [closure] :
  "[p]\<^sub>\<alpha> \<in> WF_ALPHA_REL"
  apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def)
  apply (simp add:alphabet closure)
done

theorem VarA_rel_closure [closure] :
"x \<in> REL_VAR \<Longrightarrow> VarA x \<in> REL"
apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def)
apply (simp add:alphabet closure)
done

theorem VarA_cond_closure [closure] :
"x \<in> D\<^sub>0 \<Longrightarrow> VarA x \<in> COND"
apply (simp add:WF_ALPHA_COND_def REL_ALPHABET_def)
apply (simp add:alphabet closure VarA.rep_eq)
apply (rule unrest, auto)
done

lemma SS1_alpha_image [urename]: 
  "a \<in> REL_ALPHABET \<Longrightarrow> \<langle>SS1\<rangle>\<^sub>s |`| a = (in\<^sub>\<alpha> a) |\<union>| dash |`| (out\<^sub>\<alpha> a)"
  apply (simp add:REL_ALPHABET_def)
  apply (rule fset_intro)
  apply (simp)
  apply (drule SS1_UNDASHED_DASHED_image)
  apply (simp)
done

lemma SS2_alpha_image [urename]: 
  "a \<in> REL_ALPHABET \<Longrightarrow> \<langle>SS2\<rangle>\<^sub>s |`| a = (dash |`| dash |`| (in\<^sub>\<alpha> a)) |\<union>| (out\<^sub>\<alpha> a)"
  apply (simp add:REL_ALPHABET_def)
  apply (rule fset_intro)
  apply (simp)
  apply (drule SS2_UNDASHED_DASHED_image)
  apply (auto)
done

lemma SS_alpha_image [urename]: 
  "a \<in> REL_ALPHABET \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s |`| a = dash |`| (in\<^sub>\<alpha> a) |\<union>| undash |`| (out\<^sub>\<alpha> a)"
  apply (simp add:REL_ALPHABET_def)
  apply (rule fset_intro)
  apply (simp)
  apply (drule SS_UNDASHED_DASHED_image)
  apply (simp)
done

theorem SkipA_unfold :
  assumes "a \<in> REL_ALPHABET" "x \<in> \<langle>a\<rangle>\<^sub>f" "dash x \<in> \<langle>a\<rangle>\<^sub>f" "HOM_ALPHA a"
  shows "II\<alpha>\<^bsub>a\<^esub> = (VarAE (dash x) ==\<^sub>\<alpha> VarAE x) \<and>\<^sub>\<alpha> II\<alpha>\<^bsub>(a -\<^sub>f \<lbrace>x,dash x\<rbrace>)\<^esub>"
  apply (insert assms)
  apply (utp_alpha_tac2)
  apply (rule fset_intro)
  apply (simp add:HOM_ALPHA_HOMOGENEOUS)
  apply (rule SkipRA_unfold)
  apply (auto simp add:REL_ALPHABET_def HOM_ALPHA_HOMOGENEOUS)
done

lemma EvalA_CoerceA [evala]: "\<lbrakk>(P)\<^bsub>!A\<^esub>\<rbrakk>\<pi> = (\<exists>\<^sub>p (- \<langle>A\<rangle>\<^sub>f). P)"
  by (simp add:EvalA_def CoerceA.rep_eq)

lemma CoerceA_SkipRA_right:
  "A \<in> HOM_ALPHABET \<Longrightarrow> (P)\<^bsub>!A\<^esub> = (P ;\<^sub>R II\<^bsub>\<langle>A\<rangle>\<^sub>f\<^esub>)\<^bsub>!A\<^esub>"
  apply (utp_alpha_tac)
  apply (subgoal_tac "- \<langle>A\<rangle>\<^sub>f = - \<langle>A\<rangle>\<^sub>f \<union> (D\<^sub>1 - out \<langle>A\<rangle>\<^sub>f)") 
  apply (subst SkipRA_right_as_ExistsP[of _ "D\<^sub>1"])
  apply (metis HOMOGENEOUS_HOM_ALPHA)
  apply (simp_all add: unrest)
  apply (metis ExistsP_union)
  apply (auto)
done

lemma CoerceA_SkipRA_left:
  "A \<in> HOM_ALPHABET \<Longrightarrow> (P)\<^bsub>!A\<^esub> = (II\<^bsub>\<langle>A\<rangle>\<^sub>f\<^esub> ;\<^sub>R P)\<^bsub>!A\<^esub>"
  apply (utp_alpha_tac)
  apply (subgoal_tac "- \<langle>A\<rangle>\<^sub>f = - \<langle>A\<rangle>\<^sub>f \<union> (D\<^sub>0 - in \<langle>A\<rangle>\<^sub>f)") 
  apply (subst SkipRA_left_as_ExistsP[of _ "D\<^sub>0"])
  apply (simp_all add:unrest)
  apply (metis HOMOGENEOUS_HOM_ALPHA)
  apply (metis ExistsP_union)
  apply (auto)
done

theorem CoerceA_SkipA: "A \<in> HOM_ALPHABET \<Longrightarrow> (II)\<^bsub>!A \<^esub>= II\<alpha>\<^bsub>A\<^esub>"
  apply (subst CoerceA_SkipRA_left)
  apply (simp_all)
  apply (metis CoerceA_alphabet CoerceA_rep_eq_simple SkipA.rep_eq SkipA_alphabet UNREST_SkipRA uapred_neq_elim snd_conv)
done

end


(*
theorem SemiA_algebraic:
  assumes "p \<in> WF_ALPHA_REL" "q \<in> WF_ALPHA_REL"
  shows "p ;\<^sub>\<alpha> q = (\<exists>-\<^sub>\<alpha> dash |`| out\<^sub>\<alpha> (\<alpha> p) |\<union>| dash |`| dash |`| in\<^sub>\<alpha>(\<alpha> q). (SS1\<bullet>p) \<and>\<^sub>\<alpha> (SS2\<bullet>q))"
proof -

  from assms have "\<alpha> (p ;\<^sub>\<alpha> q) = \<alpha> (\<exists>-\<^sub>\<alpha> dash |`| out\<^sub>\<alpha>(\<alpha> p) |\<union>| dash |`| dash |`| in\<^sub>\<alpha>(\<alpha> q). (SS1\<bullet>p) \<and>\<^sub>\<alpha> (SS2\<bullet>q))"
    apply (simp add:alphabet SS1_alpha_image SS2_alpha_image closure)
    apply (clarsimp)
    apply (auto simp add:var_simps var_dist var_member var_contra)
    apply (metis (lifting) DASHED_dash_elim not_dash_dash_member_out set_rev_mp utp_var.out_DASHED)
  done

  moreover
  have "\<lbrakk>p ;\<^sub>\<alpha> q\<rbrakk>\<pi> = \<lbrakk>(\<exists>-\<^sub>\<alpha> dash |`| out\<^sub>\<alpha> (\<alpha> p) |\<union>| dash |`| dash |`| in\<^sub>\<alpha>(\<alpha> q). (SS1\<bullet>p) \<and>\<^sub>\<alpha> (SS2\<bullet>q))\<rbrakk>\<pi>"
  proof -

    from assms have "\<lbrakk>p ;\<^sub>\<alpha> q\<rbrakk>\<pi> = \<pi> p ; \<pi> q"
      apply (utp_alpha_tac)
      apply (simp add:EvalA_def)
    done

    also from assms have "... = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>\<pi> p) \<and>\<^sub>p (SS2\<bullet>\<pi> q))"
      by (simp add: SemiR_algebraic unrest)

    also from assms have "... = (\<exists>\<^sub>p (DASHED_TWICE - dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f)
                              . \<exists>\<^sub>p (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f). ((SS1\<bullet>\<pi> p) \<and>\<^sub>p (SS2\<bullet>\<pi> q)))"
    proof -
      have " (DASHED_TWICE - dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f) \<union> (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f) 
           = DASHED_TWICE"
        by (auto simp add:var_defs)

      thus ?thesis
        by (metis (no_types) ExistsP_union)
    qed

    also from assms have "... = (\<exists>\<^sub>p (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f) . (SS1\<bullet>\<pi> p) \<and>\<^sub>p (SS2\<bullet> \<pi> q))"
    proof -
      from assms have "(D\<^sub>2 - (dash ` out \<langle>\<alpha> p\<rangle>\<^sub>f \<union> dash ` dash ` in \<langle>\<alpha> q\<rangle>\<^sub>f)) \<sharp> ((SS1\<bullet>\<pi> p) \<and>\<^sub>p \<pi> (SS2\<bullet>q))"
        apply (rule_tac unrest)
        apply (rule_tac unrest)
        apply (rule WF_ALPHA_PREDICATE_UNREST)
        apply (simp add:rename_dist rename_simps SS1_UNDASHED_DASHED_image[simplified] closure)
        apply (auto intro:unrest)[1]
        apply (rule UNREST_subset)
        apply (rule WF_ALPHA_PREDICATE_UNREST)
        apply (simp add:rename_dist rename_simps SS2_UNDASHED_DASHED_image[simplified] closure)
        apply (auto)[1]
        apply (auto simp add:alphabet)
        apply (metis (full_types) DASHED_TWICE_undash_DASHED DASHED_undash_UNDASHED Int_iff SS2_DASHED_TWICE_app SS2_UNDASHED_app SS2_ident_app UNDASHED_not_DASHED_TWICE imageI in_vars_def)
      done

      thus ?thesis
        apply (rule_tac ExistsP_ident)
        apply (rule unrest)
        apply (rule unrest)
        sorry
    qed

    ultimately show ?thesis
      by (utp_alpha_tac, simp add:EvalA_def)
  qed

  ultimately show ?thesis
    by (rule EvalA_intro)

qed
*)
