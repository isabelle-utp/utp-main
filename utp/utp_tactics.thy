(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_tactics.thy                                                      *)
(* Authors: Simon Foster & Frank Zeyda (University of York, UK)               *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 12 Jan 2017 *)

section {* Supplementary Tactics *}

theory utp_tactics
imports utp_rel
keywords "update_uexpr_rep_eq" :: thy_decl
begin

subsection {* Fast Transfer Tactics *}

ML_file "utp_tactics.ML"

text {*
  We configure a dynamic attribute @{text uexpr_rep_eq} in order to collect all
  @{text rep_eq} laws of lifted definitions on the type @{type uexpr}. These
  theorems are later used to implement a less powerful but transfer tactic for
  predicate equalities and refinements.
*}

setup {*
  Global_Theory.add_thms_dynamic (@{binding uexpr_rep_eq},
    UTP_Tactics.get_uexpr_rep_eq_thms o Context.proof_of)
*}

text {*
  The below configures the @{command update_uexpr_rep_eq} command; it is used
  to update the content of the @{text uexpr_rep_eq} attribute. Although the
  relevant theorems are collected automatically, for efficiency reasons the
  user has to manually trigger this process. The command below should thus
  be executed whenever additional lifted definitions on the @{type uexpr} type
  are defined.
*}

ML {*
  Outer_Syntax.command @{command_keyword update_uexpr_rep_eq}
    "update uexpr_rep_eq attribute"
    (Scan.succeed (Toplevel.keep
      (UTP_Tactics.update_uexpr_rep_eq_thms o Toplevel.context_of)));
*}

text {*
  Lastly, we re-implement the automatic tactics using fast transfer. This does
  not always seem to work in place of the original tactics but appears to do
  so in about 95\% of the cases. Perhaps some more investigation could enhance
  the tactics towards 100\% coverage.
*}

method fast_pred_simp = (
  (unfold upred_defs)?,
  -- {* The tactic below is much faster than the general transfer tactic. *}
  (simp add: uexpr_eq_iff uexpr_rep_eq)?,
  (simp add: fun_eq_iff
    lens_defs upred_defs alpha_splits Product_Type.split_beta)?,
  (simp add: lens_interp_laws)?,
  (clarsimp)?)

method fast_pred_auto = (fast_pred_simp, auto?)
method fast_pred_blast = (fast_pred_simp; blast)

method fast_rel_simp = (
  (unfold upred_defs urel_defs)?,
  -- {* The tactic below is much faster than the general transfer tactic. *}
  (simp add: uexpr_eq_iff uexpr_rep_eq)?,
  (simp add: fun_eq_iff relcomp_unfold OO_def
    lens_defs uvar_defs upred_defs alpha_splits Product_Type.split_beta)?,
  (simp add: lens_interp_laws)?,
  (clarsimp)?)

method fast_rel_auto = (fast_rel_simp, auto?)
method fast_rel_blast = (fast_rel_simp; blast)
end