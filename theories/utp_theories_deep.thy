(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_theories_deep.thy                                                *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section {* UTP Theories Supplement for Deep Variables *}

theory utp_theories_deep
imports utp_theories "UTP-Deep.utp_deep"
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

end