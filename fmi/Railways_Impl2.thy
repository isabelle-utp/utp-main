(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Railways_Impl.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 22 Sep 2017 *)

section {* Railways Implementation *}

theory Railways_Impl2
imports Topology utp_hoare_ext
begin

declare [[syntax_ambiguity_warning=false]]

subsection {* Interlocking FMU *}

subsubsection {* Interlocking State *}

type_synonym TIME = "nat"

  alphabet ilock_state =
    (* Input Variables *)
    cdv :: "bool vector"
    tc :: "bool vector"
    (* Output Variables *)
    signals :: "bool vector"
    switches :: "switch vector"
    (* Interlocking State *)
    relays :: "bool vector"
    (* Simulation Time *)
    time :: "TIME"

text \<open>Convenience syntax for indexed access of @{const cdv}.\<close>

abbreviation CDV :: "nat \<Rightarrow> (bool, ilock_state) uexpr" ("CDV[_]") where
"CDV[i] \<equiv> &cdv[i]\<^sub>u"

text \<open>Convenience syntax for indexed access of @{const tc}.\<close>

abbreviation TC :: "nat \<Rightarrow> (bool, ilock_state) uexpr" ("TC[_]") where
"TC[i] \<equiv> &tc[i]\<^sub>u"

text \<open>Convenience syntax for accessing elements of @{const relays}.\<close>

abbreviation "R1 \<equiv> &relays[1]\<^sub>u"
abbreviation "R2 \<equiv> &relays[2]\<^sub>u"
abbreviation "R3 \<equiv> &relays[3]\<^sub>u"
abbreviation "R4 \<equiv> &relays[4]\<^sub>u"
abbreviation "R5 \<equiv> &relays[5]\<^sub>u"

text \<open>Convenience syntax for accessing elements of @{const switches}.\<close>

abbreviation "SW1 \<equiv> &switches[1]\<^sub>u"
abbreviation "SW2 \<equiv> &switches[2]\<^sub>u"
abbreviation "SW3 \<equiv> &switches[3]\<^sub>u"
abbreviation "SW4 \<equiv> &switches[4]\<^sub>u"
abbreviation "SW5 \<equiv> &switches[5]\<^sub>u"

subsubsection {* Initialisation *}

definition init_ilock :: "ilock_state hrel" where [urel_defs]:
"init_ilock =
  (cdv, tc, relays, signals, switches) := (
    mk_vector\<^sub>u 11 true,
    mk_vector\<^sub>u 4 false,
    mk_vector\<^sub>u 5 false,
    mk_vector\<^sub>u 3 false,
    mk_vector\<^sub>u 5 \<guillemotleft>STRAIGHT\<guillemotright>)"

subsubsection {* Cyclic Behaviour *}

paragraph {* Relay Setting *}

definition set_relays :: "ilock_state hrel" where
[urel_defs]: "set_relays =
  ((relays[1] := true) \<triangleleft> TC[4] \<and> \<not> TC[3] \<and> \<not> R2 \<and> \<not> R4 \<and>
    (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[5] \<triangleright>\<^sub>r II) ;;
  ((relays[2] := true) \<triangleleft> TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R3 \<and> \<not> R4 \<and> \<not> R5 \<and>
    (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[10] \<and> CDV[1] \<triangleright>\<^sub>r II) ;;
  ((relays[4] := true) \<triangleleft> TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R5 \<and>
    (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[11] \<and> CDV[2] \<triangleright>\<^sub>r II) ;;
  ((relays[3] := true) \<triangleleft> TC[1] \<and> \<not> R2 \<and> \<not> R4 \<and> \<not> R5 \<and>
    (*\<not> CDV[1] \<and>*) CDV[10] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6] \<triangleright>\<^sub>r II) ;;
  ((relays[5] := true) \<triangleleft> TC[2] \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R4 \<and>
    (*\<not> CDV[2] \<and>*) CDV[11] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6] \<triangleright>\<^sub>r II)"

paragraph {* Relay Clearing *}

definition clear_relays :: "ilock_state hrel" where
[urel_defs]: "clear_relays =
  ((relays[1] := false) \<triangleleft> R1 \<and> \<not> CDV[5] \<triangleright>\<^sub>r II) ;;
  ((relays[2] := false) \<triangleleft> R2 \<and> \<not> CDV[1] \<triangleright>\<^sub>r II) ;;
  ((relays[3] := false) \<triangleleft> R3 \<and> \<not> CDV[6] \<triangleright>\<^sub>r II) ;;
  ((relays[4] := false) \<triangleleft> R4 \<and> \<not> CDV[2] \<triangleright>\<^sub>r II) ;;
  ((relays[5] := false) \<triangleleft> R5 \<and> \<not> CDV[6] \<triangleright>\<^sub>r II)"

paragraph {* Switch Setting *}

definition set_switches :: "ilock_state hrel" where
[urel_defs]: "set_switches = (
  (switches[1] := \<guillemotleft>STRAIGHT\<guillemotright>) ;;
  ((switches[2] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> R3 \<or> R5 \<triangleright>\<^sub>r (switches[2] := \<guillemotleft>DIVERGING\<guillemotright>)) ;;
  ((switches[3] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> R1 \<triangleright>\<^sub>r (switches[3] := \<guillemotleft>DIVERGING\<guillemotright>)) ;;
  (switches[4] := \<guillemotleft>STRAIGHT\<guillemotright>) ;;
  ((switches[5] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> R2 \<or> R3 \<triangleright>\<^sub>r (switches[5] := \<guillemotleft>DIVERGING\<guillemotright>)))"

subsubsection {* Signal Setting *}

definition set_signals :: "ilock_state hrel" where
[urel_defs]: "set_signals = (
  (signals[1] := (R3 \<and> SW5 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW4 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>)) ;;
  (signals[2] := (R5 \<and> SW5 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW4 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>)) ;;
  (signals[3] := ((R1 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>) \<or>
    (R2 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW5 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>) \<or>
    (R4 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW5 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright>))))"

paragraph {* Complete Cycle *}

consts \<delta> :: "(TIME, 'a) uexpr"

definition ilock_cycle :: "ilock_state hrel" where
[urel_defs]: "ilock_cycle =
  (set_relays ;; clear_relays ;; set_switches ;; set_signals ;; time := (&time + \<delta>))"
end