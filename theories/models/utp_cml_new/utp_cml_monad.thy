(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_expr.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Monad *}

theory utp_cml_monad
imports 
  utp_cml_sorts
begin

(* CML expressions and CML predicates *)

type_synonym 'a cmle         = "('a option, cmlm) pexpr"
type_synonym cmlb            = "cmlm binding"
type_synonym cmlp            = "cmlm upred" 
type_synonym 'a cmlvar       = "('a option, cmlm) pvar"
type_synonym cmluvar         = "cmlm uvar"
type_synonym 'a cmlopb       = "('a option, cmlm) WF_OPERATION"
type_synonym ('a, 'b) cmlop  = "'b cmlvar \<Rightarrow> 'a \<Rightarrow> cmlp"
type_synonym cmlev           = "cmlm event"
type_synonym 'a cmlch        = "'a chan"

translations
  (type) "'a cmle" <= (type) "('a option, cmlm) pexpr"
  (type) "cmlb" <= (type) "cmlm binding"
  (type) "cmlp" <= (type) "cmlm upred"
  (type) "'a cmlvar" <= (type) "('a option, cmlm) pvar"
  (type) "('a, 'b) cmlop" <= (type) "'a cmle \<Rightarrow> 'b cmlvar \<times> bool \<Rightarrow> cmlp"
  (type) "cmlev" <= (type) "cmlv event"

text {* Monadic bind for finite sets *}

definition fset_bind :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b fset) \<Rightarrow> 'b fset" where
"fset_bind A f = \<Union>\<^sub>f (f |`| A)"

lift_definition fset_comp :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b fset" is
"\<lambda> f A P. {f(x) | x. x \<in> A \<and> P(x)}"
  by (auto)

adhoc_overloading
  bind fset_bind

definition map_fset_option :: "('a option) fset \<Rightarrow> 'a fset option" where
"map_fset_option xs = (if (None |\<in>| xs) then None else Some (the |`| xs))"

definition fset_iter :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b fset option" where
"fset_iter A f = map_fset_option (f |`| A)"

text {* Mondic bind for CML expressions *}

definition cmle_bind :: "'a cmle \<Rightarrow> ('a \<Rightarrow> 'b cmle) \<Rightarrow> 'b cmle" where
"cmle_bind v F = MkPExpr (\<lambda> b. do { x <- \<lbrakk>v\<rbrakk>\<^sub>*b; \<lbrakk>F x\<rbrakk>\<^sub>*b })"

definition cmle_fset_iter :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b cmle) \<Rightarrow> 'b fset cmle" where
"cmle_fset_iter A F = MkPExpr (\<lambda> b. map_fset_option ((\<lambda> x. \<lbrakk>F(x)\<rbrakk>\<^sub>*b) |`| A))"

definition cmle_bset_iter :: "'a bset \<Rightarrow> ('a \<Rightarrow> 'b cmle) \<Rightarrow> 'b bset cmle" where
"cmle_bset_iter A F = MkPExpr (\<lambda> b. bset_option (bset_image (\<lambda> x. \<lbrakk>F(x)\<rbrakk>\<^sub>*b) A))"

adhoc_overloading
  bind cmle_bind

lemma EvalD_cmle_bind [evalp]: 
  "\<lbrakk>x >>= f\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>*b >>= (\<lambda> x. \<lbrakk>f(x)\<rbrakk>\<^sub>*b))"
  by (simp add:cmle_bind_def)

lemma EvalD_cmle_fset_iter [evalp]: 
  "\<lbrakk>cmle_fset_iter A F\<rbrakk>\<^sub>*b = map_fset_option ((\<lambda>x. \<lbrakk>F(x)\<rbrakk>\<^sub>* b) |`| A)"
  by (simp add: cmle_fset_iter_def)

lemma EvalD_cmle_bset_iter [evalp]: 
  "\<lbrakk>cmle_bset_iter A F\<rbrakk>\<^sub>*b = bset_option (bset_image (\<lambda>x. \<lbrakk>F(x)\<rbrakk>\<^sub>* b) A)"
  by (simp add: cmle_bset_iter_def)
  
end
