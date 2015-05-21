(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_monad.thy                                                    *)
(* Authors: Original CML model by Simon Foster, University of York (UK)       *)
(*          Adapted to VDM by Luis Diogo Couto, Aarhus University (DK)        *)
(******************************************************************************)

header {* VDM Monad *}

theory utp_vdm_monad
imports 
  utp_vdm_sorts
begin

(* VDM expressions and VDM predicates *)

type_synonym 'a vdme         = "('a option, vdmm) pexpr"
type_synonym vdmb            = "vdmm binding"
type_synonym vdmp            = "vdmm upred" 
type_synonym 'a vdmvar       = "('a option, vdmm) pvar"
type_synonym vdmuvar         = "vdmm uvar"
type_synonym 'a vdmopb       = "('a option, vdmm) WF_OPERATION"
type_synonym ('a, 'b) vdmop  = "'b vdmvar \<Rightarrow> 'a \<Rightarrow> vdmp"

translations
  (type) "'a vdme" <= (type) "('a option, vdmm) pexpr"
  (type) "vdmb" <= (type) "vdmm binding"
  (type) "vdmp" <= (type) "vdmm upred"
  (type) "'a vdmvar" <= (type) "('a option, vdmm) pvar"
  (type) "('a, 'b) vdmop" <= (type) "'a vdme \<Rightarrow> 'b vdmvar \<times> bool \<Rightarrow> vdmp"

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

text {* Mondic bind for VDM expressions *}

definition vdme_bind :: "'a vdme \<Rightarrow> ('a \<Rightarrow> 'b vdme) \<Rightarrow> 'b vdme" where
"vdme_bind v F = MkPExpr (\<lambda> b. do { x <- \<lbrakk>v\<rbrakk>\<^sub>*b; \<lbrakk>F x\<rbrakk>\<^sub>*b })"

definition vdme_fset_iter :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b vdme) \<Rightarrow> 'b fset vdme" where
"vdme_fset_iter A F = MkPExpr (\<lambda> b. map_fset_option ((\<lambda> x. \<lbrakk>F(x)\<rbrakk>\<^sub>*b) |`| A))"

definition vdme_bset_iter :: "'a bset \<Rightarrow> ('a \<Rightarrow> 'b vdme) \<Rightarrow> 'b bset vdme" where
"vdme_bset_iter A F = MkPExpr (\<lambda> b. bset_option (bset_image (\<lambda> x. \<lbrakk>F(x)\<rbrakk>\<^sub>*b) A))"

adhoc_overloading
  bind vdme_bind

lemma EvalD_vdme_bind [evalp]: 
  "\<lbrakk>x >>= f\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>*b >>= (\<lambda> x. \<lbrakk>f(x)\<rbrakk>\<^sub>*b))"
  by (simp add:vdme_bind_def)

lemma EvalD_vdme_fset_iter [evalp]: 
  "\<lbrakk>vdme_fset_iter A F\<rbrakk>\<^sub>*b = map_fset_option ((\<lambda>x. \<lbrakk>F(x)\<rbrakk>\<^sub>* b) |`| A)"
  by (simp add: vdme_fset_iter_def)

lemma EvalD_vdme_bset_iter [evalp]: 
  "\<lbrakk>vdme_bset_iter A F\<rbrakk>\<^sub>*b = bset_option (bset_image (\<lambda>x. \<lbrakk>F(x)\<rbrakk>\<^sub>* b) A)"
  by (simp add: vdme_bset_iter_def)
  
end
