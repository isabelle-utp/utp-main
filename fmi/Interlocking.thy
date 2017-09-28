(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Interlocking.thy                                                     *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 22 Sep 2017 *)

section {* Interlocking FMU Model *}

theory Interlocking
imports Vector Topology utp_hoare_ext
begin recall_syntax

(* declare One_nat_def [simp del] *)

subsection {* Interlocking State *}

alphabet ilock_state =
  cdv :: "bool vector"
  tc :: "bool vector"
  relays :: "bool vector"
  signals :: "bool vector"
  switches :: "switch vector"

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

subsection {* Proof Support *}

text \<open>Interpretations for the @{type ilock_state} alphabet type.\<close>

interpretation ilock_var_interp1:
  lens_interp "\<lambda>r. (cdv\<^sub>v r, tc\<^sub>v r, relays\<^sub>v r, signals\<^sub>v r, switches\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation ilock_var_interp2:
  lens_interp "\<lambda>(r, r'). (cdv\<^sub>v r, cdv\<^sub>v r', tc\<^sub>v r, tc\<^sub>v r', relays\<^sub>v r, relays\<^sub>v r',
    signals\<^sub>v r, signals\<^sub>v r', switches\<^sub>v r, switches\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsection {* Initial State *}

definition init_ilock :: "ilock_state hrel" where [urel_defs]:
"init_ilock =
  (cdv, tc, relays, signals, switches) := (
    mk_vector\<^sub>u 11 true,
    mk_vector\<^sub>u 4 false,
    mk_vector\<^sub>u 5 false,
    mk_vector\<^sub>u 3 false,
    mk_vector\<^sub>u 5 \<guillemotleft>STRAIGHT\<guillemotright>)"

subsection {* Cyclic Behaviour *}

text \<open>We break down the cyclic behaviour into four separate operations.\<close>

subsubsection {* Relay Setting *}

definition set_relays :: "ilock_state hrel" where
[urel_defs]: "set_relays =
  ((relays[1] := true) \<triangleleft> TC[4] \<and> \<not> TC[3] \<and> \<not> R2 \<and> \<not> R4 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[5] \<triangleright>\<^sub>r II) ;;
  ((relays[2] := true) \<triangleleft> TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R3 \<and> \<not> R4 \<and> \<not> R5 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[10] \<and> CDV[1] \<triangleright>\<^sub>r II) ;;
  ((relays[4] := true) \<triangleleft> TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R5 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[11] \<and> CDV[2] \<triangleright>\<^sub>r II) ;;
  ((relays[3] := true) \<triangleleft> TC[1] \<and> \<not> R2 \<and> \<not> R4 \<and> \<not> R5 \<and> (*\<not> CDV[1] \<and>*) CDV[10] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6] \<triangleright>\<^sub>r II) ;;
  ((relays[5] := true) \<triangleleft> TC[2] \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R4 \<and> (*\<not> CDV[2] \<and>*) CDV[11] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6] \<triangleright>\<^sub>r II)"

subsubsection {* Relay Clearing *}

definition clear_relays :: "ilock_state hrel" where
[urel_defs]: "clear_relays =
  ((relays[1] := false) \<triangleleft> R1 \<and> \<not> CDV[5] \<triangleright>\<^sub>r II) ;;
  ((relays[2] := false) \<triangleleft> R2 \<and> \<not> CDV[1] \<triangleright>\<^sub>r II) ;;
  ((relays[3] := false) \<triangleleft> R3 \<and> \<not> CDV[6] \<triangleright>\<^sub>r II) ;;
  ((relays[4] := false) \<triangleleft> R4 \<and> \<not> CDV[2] \<triangleright>\<^sub>r II) ;;
  ((relays[5] := false) \<triangleleft> R5 \<and> \<not> CDV[6] \<triangleright>\<^sub>r II)"

subsubsection {* Switch Setting *}

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

subsubsection {* Complete Cycle *}

definition ilock_cycle :: "ilock_state hrel" where [urel_defs]:
"ilock_cycle = (set_relays ;; clear_relays ;; set_switches ;; set_signals)"

subsection {* Invariants *}

text \<open>We next prove several invariants of the interlocking model.\<close>

subsubsection {* Type Invariant *}

text \<open>The type invariant establishes that all vectors have the correct size.\<close>

definition ilock_type_inv :: "ilock_state upred" where [urel_defs]:
"ilock_type_inv = (
  #\<^sub>u(&cdv) =\<^sub>u 11 \<and>
  #\<^sub>u(&tc) =\<^sub>u 4 \<and>
  #\<^sub>u(&relays) =\<^sub>u 5 \<and>
  #\<^sub>u(&signals) =\<^sub>u 3 \<and>
  #\<^sub>u(&switches) =\<^sub>u 5)"

text {* Method for proving the interlocking type invariant. *}

lemma ilock_type_inv_rules:
"\<lbrace>ilock_type_inv\<rbrace>S\<lbrace>ilock_type_inv\<rbrace>\<^sub>u \<Longrightarrow>
 \<lbrace>ilock_type_inv \<and> P\<rbrace>S\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
"`ilock_type_inv \<Rightarrow> s \<dagger> ilock_type_inv` \<Longrightarrow>
 `ilock_type_inv \<and> P \<Rightarrow> s \<dagger> ilock_type_inv`"
apply (rel_simp)+
done

text {* The tactic below is a bit quicker than @{method hoare_auto}. *}

method ilock_type_inv_tac =
  (hoare_split_inv add: ilock_type_inv_rules; rel_simp)

lemma init_ilock_type_inv:
"\<lbrace>true\<rbrace>init_ilock\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
apply (rel_simp)
done

lemma set_relays_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_relays\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding set_relays_def by (hoare_auto) *)
  unfolding set_relays_def by (ilock_type_inv_tac)

lemma clear_relays_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>clear_relays\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding clear_relays_def by (hoare_auto) *)
  unfolding clear_relays_def by (ilock_type_inv_tac)

lemma set_switches_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_switches\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding set_switches_def by (hoare_auto) *)
  unfolding set_switches_def by (ilock_type_inv_tac)

lemma set_signals_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_signals\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
(* unfolding set_signals_def by (hoare_auto) *)
  unfolding set_signals_def by (ilock_type_inv_tac)

lemma "\<lbrace>ilock_type_inv\<rbrace>ilock_cycle\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
apply (unfold ilock_cycle_def)
apply (hoare_split)
apply (rule set_relays_type_inv)
apply (rule clear_relays_type_inv)
apply (rule set_switches_type_inv)
apply (rule set_signals_type_inv)
done

subsubsection {* Relays Invariant *}

text \<open>Ensures that at most one relay can be activated at a time.\<close>

definition relays_excl_inv :: "ilock_state upred" where [upred_defs]:
"relays_excl_inv = (
  (#\<^sub>u(&relays) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
  (R1 \<Rightarrow> \<not> R2 \<and> \<not> R4) \<and>
  (R2 \<Rightarrow> \<not> R1 \<and> \<not> R3 \<and> \<not> R4 \<and> \<not> R5) \<and>
  (R4 \<Rightarrow> \<not> R1 \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R5) \<and>
  (R3 \<Rightarrow> \<not> R2 \<and> \<not> R4 \<and> \<not> R5) \<and>
  (R5 \<Rightarrow> \<not> R2 \<and> \<not> R3 \<and> \<not> R4))"

paragraph {* Proof Support *}

definition valid_relay_states :: "(bool vector) set" where
"valid_relay_states =
 vector_from_list ` {
  [OFF, OFF, OFF, OFF, OFF],
  [ON, OFF, OFF, OFF, OFF],
  [ON, OFF, OFF, OFF, ON],
  [ON, OFF, ON, OFF, OFF],
  [OFF, ON, OFF, OFF, OFF],
  [OFF, OFF, ON, OFF, OFF],
  [ON, OFF, ON, OFF, OFF],
  [OFF, OFF, OFF, ON, OFF],
  [OFF, OFF, OFF, OFF, ON],
  [ON, OFF, OFF, OFF, ON]}"

lemma eq_vector_from_list_5:
"size v = 5 \<Longrightarrow>
  (v = vector_from_list [b1, b2, b3, b4, b5]) =
  (v\<^bold>[1\<^bold>] = b1 \<and> v\<^bold>[2\<^bold>] = b2 \<and> v\<^bold>[3\<^bold>] = b3 \<and> v\<^bold>[4\<^bold>] = b4 \<and> v\<^bold>[5\<^bold>] = b5)"
apply (subst vector_equality)
apply (clarsimp)
apply (safe; clarsimp)
apply (subgoal_tac "i \<in> {1, 2, 3, 4, 5}")
apply (safe; clarsimp)
apply (safe; clarsimp)
done

lemma relays_excl_inv_cases:
"relays_excl_inv = (&relays \<in>\<^sub>u \<guillemotleft>valid_relay_states\<guillemotright>)"
apply (unfold relays_excl_inv_def)
apply (rel_simp)
apply (safe; clarsimp?)
apply (unfold valid_relay_states_def)
apply (simp_all add: eq_vector_from_list_5)
apply (safe; clarsimp)+
done

lemma relays_excl_inv_split:
"`relays_excl_inv \<Rightarrow> P` = `\<^bold>\<forall> v\<in>\<guillemotleft>valid_relay_states\<guillemotright> \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright> / &relays\<rbrakk>`"
apply (unfold relays_excl_inv_cases)
apply (pred_simp robust)
apply (safe; clarsimp)
done

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

subsection {* Proof Experiments *}

lemma uvector_from_list_simps [simp]:
"i \<in> {1..length l} \<Longrightarrow> (vector_from_list\<^sub>u l)[i]\<^sub>u = \<guillemotleft>l ! (i - 1)\<guillemotright>"
apply (pred_simp)
done
end