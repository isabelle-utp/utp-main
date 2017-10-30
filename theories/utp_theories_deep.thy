(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_theories_deep.thy                                                *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section {* UTP Theories Supplement for Deep Variables *}

theory utp_theories_deep
imports utp_theories "../utp/models/utp_deep"
begin

subsection {* Instantiation of @{class vst}. *}

text {* Instantiate the vstore for design alphabets. *}

instantiation des_vars_ext :: (vst) vst
begin
  definition vstore_lens_des_vars_ext :: "vstore \<Longrightarrow> 'a des_vars_ext" where
  "vstore_lens_des_vars_ext = \<V> ;\<^sub>L \<Sigma>\<^sub>D"
instance
  by (intro_classes, simp add: vstore_lens_des_vars_ext_def)
end

text {* Instantiate the vstore for reactive alphabets. *}

instantiation rp_vars_ext :: (trace,vst) vst
begin
  definition vstore_lens_rp_vars_ext :: "vstore \<Longrightarrow> ('a, 'b) rp_vars_ext" where
  "vstore_lens_rp_vars_ext = \<V> ;\<^sub>L \<Sigma>\<^sub>r"
instance
  by (intro_classes, simp add: vstore_lens_rp_vars_ext_def)
end

text {* Instantiate the vstore for stateful reactive alphabets. *}

instantiation rsp_vars_ext :: (vst,type) vst
begin
  definition vstore_lens_rsp_vars_ext :: "vstore \<Longrightarrow> ('a, 'b) rsp_vars_scheme" where
  "vstore_lens_rsp_vars_ext = \<V> ;\<^sub>L st\<^sub>a"
instance
  by (intro_classes, simp add: vstore_lens_rsp_vars_ext_def)
end

subsection {* Procedure Declarations *}

text {* We also set up procedures for the theory of designs. *}

abbreviation "DAL \<equiv> TYPE(DES \<times> '\<alpha> des \<times> '\<alpha>)"
abbreviation "NDAL \<equiv> TYPE(NDES \<times> '\<alpha> des \<times> '\<alpha>)"

syntax
 "_dproc_block"  :: "parm_list \<Rightarrow> logic \<Rightarrow> ('a, '\<alpha>) uproc" ("_ \<bullet>\<^sub>D/ _" [0,10] 10)
 "_nproc_block"  :: "parm_list \<Rightarrow> logic \<Rightarrow> ('a, '\<alpha>) uproc" ("_ \<bullet>\<^sub>N/ _" [0,10] 10)

translations
  "_dproc_block ps P" => "_proc_block (CONST DAL) ps P"
  "_nproc_block ps P" => "_proc_block (CONST NDAL) ps P"
end