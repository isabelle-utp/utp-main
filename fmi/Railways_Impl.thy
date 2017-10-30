(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Railways_Impl.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 22 Sep 2017 *)

section {* Railways Implementation *}

theory Railways_Impl
imports Railways_Spec
begin

subsection {* Interlocking FMU *}

subsubsection {* Initialisation *}

definition init_ilock :: "railways_state hrel" where [urel_defs]:
"init_ilock =
  (cdv, tc, relays, signals, switches) := (
    mk_vector\<^sub>u 11 true,
    mk_vector\<^sub>u 4 false,
    mk_vector\<^sub>u 5 false,
    mk_vector\<^sub>u 3 false,
    mk_vector\<^sub>u 5 \<guillemotleft>STRAIGHT\<guillemotright>)"

subsubsection {* Cyclic Behaviour *}

paragraph {* Relay Setting *}

definition set_relays :: "railways_state hrel" where
[urel_defs]: "set_relays =
  ((relays[1] := true) \<triangleleft> TC[4] \<and> \<not> TC[3] \<and> \<not> R2 \<and> \<not> R4 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[5] \<triangleright>\<^sub>r II) ;;
  ((relays[2] := true) \<triangleleft> TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R3 \<and> \<not> R4 \<and> \<not> R5 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[10] \<and> CDV[1] \<triangleright>\<^sub>r II) ;;
  ((relays[4] := true) \<triangleleft> TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R5 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[11] \<and> CDV[2] \<triangleright>\<^sub>r II) ;;
  ((relays[3] := true) \<triangleleft> TC[1] \<and> \<not> R2 \<and> \<not> R4 \<and> \<not> R5 \<and> (*\<not> CDV[1] \<and>*) CDV[10] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6] \<triangleright>\<^sub>r II) ;;
  ((relays[5] := true) \<triangleleft> TC[2] \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R4 \<and> (*\<not> CDV[2] \<and>*) CDV[11] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6] \<triangleright>\<^sub>r II)"

paragraph {* Relay Clearing *}

definition clear_relays :: "railways_state hrel" where
[urel_defs]: "clear_relays =
  ((relays[1] := false) \<triangleleft> R1 \<and> \<not> CDV[5] \<triangleright>\<^sub>r II) ;;
  ((relays[2] := false) \<triangleleft> R2 \<and> \<not> CDV[1] \<triangleright>\<^sub>r II) ;;
  ((relays[3] := false) \<triangleleft> R3 \<and> \<not> CDV[6] \<triangleright>\<^sub>r II) ;;
  ((relays[4] := false) \<triangleleft> R4 \<and> \<not> CDV[2] \<triangleright>\<^sub>r II) ;;
  ((relays[5] := false) \<triangleleft> R5 \<and> \<not> CDV[6] \<triangleright>\<^sub>r II)"

paragraph {* Switch Setting *}

definition set_switches :: "railways_state hrel" where
[urel_defs]: "set_switches = (
  (switches[1] := \<guillemotleft>STRAIGHT\<guillemotright>) ;;
  ((switches[2] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> R3 \<or> R5 \<triangleright>\<^sub>r (switches[2] := \<guillemotleft>DIVERGING\<guillemotright>)) ;;
  ((switches[3] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> R1 \<triangleright>\<^sub>r (switches[3] := \<guillemotleft>DIVERGING\<guillemotright>)) ;;
  (switches[4] := \<guillemotleft>STRAIGHT\<guillemotright>) ;;
  ((switches[5] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> R2 \<or> R3 \<triangleright>\<^sub>r (switches[5] := \<guillemotleft>DIVERGING\<guillemotright>)))"

subsubsection {* Signal Setting *}

definition set_signals :: "railways_state hrel" where
[urel_defs]: "set_signals = (
  (signals[1] := (R3 \<and> SW5 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW4 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>)) ;;
  (signals[2] := (R5 \<and> SW5 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW4 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>)) ;;
  (signals[3] := ((R1 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>) \<or>
    (R2 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW5 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>) \<or>
    (R4 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW5 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright>))))"

paragraph {* Complete Cycle *}

definition ilock_cycle :: "railways_state hrel" where [urel_defs]:
"ilock_cycle = (set_relays ;; clear_relays ;; set_switches ;; set_signals)"

subsubsection {* Invariant Proofs *}

paragraph {* Proof Support *}

lemma relays_excl_inv_extr:
"`relays_excl_inv \<and> P \<Rightarrow> Q` = `relays_excl_inv \<Rightarrow> P \<Rightarrow> Q`"
  by (simp add: impl_alt_def utp_pred_laws.sup.assoc)

text {* Do \<open>,\<close>  and \<open>;\<close> have the same precedence? Are they right-associative? *}

method ilock_relays_excl_inv_tac =
  (hoare_split_inv; (
    (unfold relays_excl_inv_extr)?,
    (unfold relays_excl_inv_cases),
    (rel_simp);
    (unfold valid_relay_states_def),
    (safe; simp)))

paragraph {* Invariant Preservation *}

lemma init_ilock_relays_excl_inv:
"\<lbrace>true\<rbrace>init_ilock\<lbrace>relays_excl_inv\<rbrace>\<^sub>u"
  unfolding init_ilock_def by (rel_simp)

lemma set_relays_relays_excl_inv:
"\<lbrace>relays_excl_inv\<rbrace>set_relays\<lbrace>relays_excl_inv\<rbrace>\<^sub>u"
  unfolding set_relays_def by (ilock_relays_excl_inv_tac)

lemma clear_relays_relays_excl_inv:
"\<lbrace>relays_excl_inv\<rbrace>clear_relays\<lbrace>relays_excl_inv\<rbrace>\<^sub>u"
  unfolding clear_relays_def by (ilock_relays_excl_inv_tac)

lemma set_switches_relays_excl_inv:
"\<lbrace>relays_excl_inv\<rbrace>set_switches\<lbrace>relays_excl_inv\<rbrace>\<^sub>u"
  unfolding set_switches_def by (ilock_relays_excl_inv_tac)

lemma set_signals_relays_excl_inv:
"\<lbrace>relays_excl_inv\<rbrace>set_signals\<lbrace>relays_excl_inv\<rbrace>\<^sub>u"
  unfolding set_signals_def by (ilock_relays_excl_inv_tac)

lemma "\<lbrace>relays_excl_inv\<rbrace>ilock_cycle\<lbrace>relays_excl_inv\<rbrace>\<^sub>u"
apply (unfold ilock_cycle_def)
apply (hoare_split)
apply (rule set_relays_relays_excl_inv)
apply (rule clear_relays_relays_excl_inv)
apply (rule set_switches_relays_excl_inv)
apply (rule set_signals_relays_excl_inv)
done
end