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

(* FIXME: The following command causes Isabelle to hang, consequently I've replaced it with a static
   attribute for now. *)
  
(*
setup {*
  Global_Theory.add_thms_dynamic (@{binding uexpr_rep_eq},
    UTP_Tactics.get_uexpr_rep_eq_thms o Context.proof_of)
*}
*)
  
named_theorems uexpr_rep_eq
  
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

(* FIXME: We need to manually populate the attribute until the above command is fixed *)
  
declare var.rep_eq [uexpr_rep_eq]
declare uop.rep_eq [uexpr_rep_eq]
declare bop.rep_eq [uexpr_rep_eq]
declare trop.rep_eq [uexpr_rep_eq]
declare qtop.rep_eq [uexpr_rep_eq]
declare lit.rep_eq [uexpr_rep_eq]
declare ulambda.rep_eq [uexpr_rep_eq]
declare less_eq_uexpr.rep_eq [uexpr_rep_eq]
declare ZedSetCompr.rep_eq [uexpr_rep_eq]
declare unrest_upred.rep_eq [uexpr_rep_eq]
declare subst.rep_eq [uexpr_rep_eq]
declare usubst_lookup.rep_eq [uexpr_rep_eq]
declare sup_uexpr.rep_eq [uexpr_rep_eq]
declare inf_uexpr.rep_eq [uexpr_rep_eq]
declare bot_uexpr.rep_eq [uexpr_rep_eq]
declare top_uexpr.rep_eq [uexpr_rep_eq]
declare Inf_uexpr.rep_eq [uexpr_rep_eq]
declare Sup_uexpr.rep_eq [uexpr_rep_eq]
declare USUP.rep_eq [uexpr_rep_eq]
declare UINF.rep_eq [uexpr_rep_eq]
declare impl.rep_eq [uexpr_rep_eq]
declare iff_upred.rep_eq [uexpr_rep_eq]
declare ex.rep_eq [uexpr_rep_eq]
declare shEx.rep_eq [uexpr_rep_eq]
declare all.rep_eq [uexpr_rep_eq]
declare shAll.rep_eq [uexpr_rep_eq]
declare closure.rep_eq [uexpr_rep_eq]
declare taut.rep_eq [uexpr_rep_eq]
declare seqr.rep_eq [uexpr_rep_eq]
declare conv_r.rep_eq [uexpr_rep_eq]
declare assigns_r.rep_eq [uexpr_rep_eq]
declare rel_alpha_ext.rep_eq [uexpr_rep_eq]
declare call.rep_eq [uexpr_rep_eq]
declare aext.rep_eq [uexpr_rep_eq]
declare arestr.rep_eq [uexpr_rep_eq]
  
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
    lens_defs upred_defs alpha_splits Product_Type.split_beta)?,
  (simp add: lens_interp_laws)?,
  (clarsimp)?)

method fast_rel_auto = (fast_rel_simp, auto?)
method fast_rel_blast = (fast_rel_simp; blast)
  
end