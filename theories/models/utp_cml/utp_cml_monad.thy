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

type_synonym 'a cmle         = "('a option, cmlv) pexpr"
type_synonym cmlb            = "cmlv binding"
type_synonym cmlp            = "cmlv upred" 
type_synonym 'a cmlvar       = "('a option, cmlv) pvar"
type_synonym 'a cmlopb       = "('a option, cmlv) WF_OPERATION"
type_synonym ('a, 'b) cmlop  = "('a option, 'b option, cmlv) WF_POPERATION"
type_synonym cmlev           = "cmlv EVENT"
type_synonym 'a cmlch        = "'a CHAN"

translations
  (type) "'a cmle" <= (type) "('a option, cmlv) pexpr"
  (type) "cmlb" <= (type) "cmlv binding"
  (type) "cmlp" <= (type) "cmlv upred"
  (type) "'a cmlvar" <= (type) "('a option, cmlv) pvar"
  (type) "('a, 'b) cmlop" <= (type) "'a cmle \<Rightarrow> 'b cmlvar \<times> bool \<Rightarrow> cmlp"
  (type) "cmlev" <= (type) "cmlv EVENT"

text {* Monadic bind for finite sets *}

definition fset_bind :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b fset) \<Rightarrow> 'b fset" where
"fset_bind A f = \<Union>\<^sub>f (f `\<^sub>f A)"

lift_definition fset_comp :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b fset" is
"\<lambda> f A P. {f(x) | x. x \<in> A \<and> P(x)}"
  by (simp add:fsets_def)

adhoc_overloading
  bind fset_bind

definition map_fset_option :: "('a option) fset \<Rightarrow> 'a fset option" where
"map_fset_option xs = (if (None \<in>\<^sub>f xs) then None else Some (the `\<^sub>f xs))"

definition fset_iter :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b fset option" where
"fset_iter A f = map_fset_option (f `\<^sub>f A)"

text {* Mondic bind for CML expressions *}

definition cmle_bind :: "'a cmle \<Rightarrow> ('a \<Rightarrow> 'b cmle) \<Rightarrow> 'b cmle" where
"cmle_bind v F = MkPExpr (\<lambda> b. do { x <- \<lbrakk>v\<rbrakk>\<^sub>*b; \<lbrakk>F x\<rbrakk>\<^sub>*b })"

definition cmle_fset_iter :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b cmle) \<Rightarrow> 'b fset cmle" where
"cmle_fset_iter A F = MkPExpr (\<lambda> b. map_fset_option ((\<lambda> x. \<lbrakk>F(x)\<rbrakk>\<^sub>*b) `\<^sub>f A))"

adhoc_overloading
  bind cmle_bind

lemma EvalD_cmle_bind [evalp]: 
  "\<lbrakk>x >>= f\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>*b >>= (\<lambda> x. \<lbrakk>f(x)\<rbrakk>\<^sub>*b))"
  by (simp add:cmle_bind_def)

lemma EvalD_cmle_fset_iter [evalp]: 
  "\<lbrakk>cmle_fset_iter A F\<rbrakk>\<^sub>*b = map_fset_option ((\<lambda>x. \<lbrakk>F(x)\<rbrakk>\<^sub>* b) `\<^sub>f A)"
  by (simp add: cmle_fset_iter_def)

end
