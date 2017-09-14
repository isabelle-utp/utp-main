(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Interlocking.thy                                                     *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)

subsection {* Interlocking Model *}

theory Interlocking
imports Vector "../utp/utp_hoare"
begin recall_syntax

subsection {* Type Definitions *}

text \<open>Possible configurations of railway switches.\<close> 

datatype switch =
  STRAIGHT |
  DIVERGING

subsection {* Interlocking State *}

alphabet ilock_state =
  cdv :: "bool vector"
  tc :: "bool vector"
  relays :: "bool vector"
  signals :: "bool vector"
  switches :: "switch vector"

text \<open>Convenience syntax for indexed access of @{const cdv} and @{const tc}.\<close>

abbreviation (input) CDV :: "nat \<Rightarrow> (bool, ilock_state) uexpr" ("CDV[_]") where
"CDV[i] \<equiv> &cdv[i]\<^sub>u"

abbreviation (input) TC :: "nat \<Rightarrow> (bool, ilock_state) uexpr" ("TC[_]") where
"TC[i] \<equiv> &tc[i]\<^sub>u"

text \<open>Convenience syntax for @{const relays} elements.\<close>

abbreviation "R1 \<equiv> &relays[1]\<^sub>u"
abbreviation "R2 \<equiv> &relays[2]\<^sub>u"
abbreviation "R3 \<equiv> &relays[3]\<^sub>u"
abbreviation "R4 \<equiv> &relays[4]\<^sub>u"
abbreviation "R5 \<equiv> &relays[5]\<^sub>u"

text \<open>Convenience syntax for @{const switches} elements.\<close>

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

text \<open>Available routes and their corresponding relay index.\<close>

abbreviation (input) "V1Q1 \<equiv> 1"
abbreviation (input) "V1Q2 \<equiv> 2"
abbreviation (input) "Q2V2 \<equiv> 3"
abbreviation (input) "V1Q3 \<equiv> 4"
abbreviation (input) "Q3V2 \<equiv> 5"

subsubsection {* Relay Setting *}

definition set_relays :: "ilock_state hrel" where [urel_defs]:
"set_relays =
  ((relays[1] := true) \<triangleleft> \<lceil>TC[4] \<and> \<not> TC[3] \<and> \<not> R2 \<and> \<not> R4 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[5]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[2] := true) \<triangleleft> \<lceil>TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R3 \<and> \<not> R4 \<and> \<not> R5 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[10] \<and> CDV[1]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[4] := true) \<triangleleft> \<lceil>TC[3] \<and> \<not> TC[4] \<and> \<not> R1 \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R5 \<and> (*\<not> CDV[3] \<and>*) CDV[4] \<and> CDV[8] \<and> CDV[9] \<and> CDV[11] \<and> CDV[2]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[3] := true) \<triangleleft> \<lceil>TC[1] \<and> \<not> R2 \<and> \<not> R4 \<and> \<not> R5 \<and> (*\<not> CDV[1] \<and>*) CDV[10] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[5] := true) \<triangleleft> \<lceil>TC[2] \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R4 \<and> (*\<not> CDV[2] \<and>*) CDV[11] \<and> CDV[9] \<and> CDV[8] \<and> CDV[7] \<and> CDV[6]\<rceil>\<^sub>< \<triangleright> II)"

lemma "`init_ilock ;; (tc[4] := true) ;; set_relays \<Rightarrow> $relays\<acute>[V1Q1]\<^sub>u`"
apply (rel_simp)
done

subsubsection {* Relay Clearing *}

definition reset_relays :: "ilock_state hrel" where [urel_defs]:
"reset_relays =
  ((relays[1] := false) \<triangleleft> \<lceil>R1 \<and> \<not> CDV[5]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[2] := false) \<triangleleft> \<lceil>R2 \<and> \<not> CDV[1]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[3] := false) \<triangleleft> \<lceil>R3 \<and> \<not> CDV[6]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[4] := false) \<triangleleft> \<lceil>R4 \<and> \<not> CDV[2]\<rceil>\<^sub>< \<triangleright> II) ;;
  ((relays[5] := false) \<triangleleft> \<lceil>R5 \<and> \<not> CDV[6]\<rceil>\<^sub>< \<triangleright> II)"

subsubsection {* Switch Positioning *}

definition pos_switches :: "ilock_state hrel" where [urel_defs]:
"pos_switches = (
  (switches[1] := \<guillemotleft>STRAIGHT\<guillemotright>) ;;
  ((switches[2] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> \<lceil>R3 \<or> R5\<rceil>\<^sub>< \<triangleright> (switches[2] := \<guillemotleft>DIVERGING\<guillemotright>)) ;;
  ((switches[3] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> \<lceil>R1\<rceil>\<^sub>< \<triangleright> (switches[3] := \<guillemotleft>DIVERGING\<guillemotright>)) ;;
  (switches[4] := \<guillemotleft>STRAIGHT\<guillemotright>) ;;
  ((switches[5] := \<guillemotleft>STRAIGHT\<guillemotright>) \<triangleleft> \<lceil>R2 \<or> R3\<rceil>\<^sub>< \<triangleright> (switches[5] := \<guillemotleft>DIVERGING\<guillemotright>)))"

subsubsection {* Signal Setting *}

definition set_signals :: "ilock_state hrel" where [urel_defs]:
"set_signals = (
  (signals[1] := (R3 \<and> SW5 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW4 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>)) ;;
  (signals[2] := (R5 \<and> SW5 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW4 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>)) ;;
  (signals[3] := ((R1 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>) \<or>
    (R2 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW5 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright>) \<or>
    (R4 \<and> SW1 =\<^sub>u \<guillemotleft>STRAIGHT\<guillemotright> \<and> SW3 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW2 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright> \<and> SW5 =\<^sub>u \<guillemotleft>DIVERGING\<guillemotright>)))
)"

subsubsection {* Complete Cycle *}

definition ilock_cycle :: "ilock_state hrel" where [urel_defs]:
"ilock_cycle = (set_relays ;; reset_relays ;; pos_switches ;; set_signals)"

subsection {* Invariants *}

subsubsection {* Type Invariant *}

text \<open>All vectors must have the correct size.\<close>

definition ilock_type_inv :: "ilock_state upred" where [urel_defs]:
"ilock_type_inv = (
  #\<^sub>u(&cdv) =\<^sub>u \<guillemotleft>11\<guillemotright> \<and>
  #\<^sub>u(&tc) =\<^sub>u \<guillemotleft>4\<guillemotright> \<and>
  #\<^sub>u(&relays) =\<^sub>u \<guillemotleft>5\<guillemotright> \<and>
  #\<^sub>u(&signals) =\<^sub>u \<guillemotleft>3\<guillemotright> \<and>
  #\<^sub>u(&switches) =\<^sub>u \<guillemotleft>5\<guillemotright>)"

lemma init_ilock_type_inv:
"\<lbrace>true\<rbrace>init_ilock\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
apply (rel_simp)
done
    
lemma set_relays_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_relays\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
  unfolding set_relays_def by hoare_auto

lemma reset_relays_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>reset_relays\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
  unfolding reset_relays_def by hoare_auto
    
lemma pos_switches_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>pos_switches\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
  unfolding pos_switches_def by hoare_auto

lemma set_signals_type_inv:
"\<lbrace>ilock_type_inv\<rbrace>set_signals\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
  unfolding set_signals_def by hoare_auto

lemma "\<lbrace>ilock_type_inv\<rbrace>ilock_cycle\<lbrace>ilock_type_inv\<rbrace>\<^sub>u"
apply (unfold ilock_cycle_def)
apply (rule_tac s = "ilock_type_inv" in seq_hoare_r)
apply (rule set_relays_type_inv)
apply (rule_tac s = "ilock_type_inv" in seq_hoare_r)
apply (rule reset_relays_type_inv)
apply (rule_tac s = "ilock_type_inv" in seq_hoare_r)
apply (rule pos_switches_type_inv)
apply (rule set_signals_type_inv)
done

subsubsection {* Relays Invariant *}

text \<open>At most one relay is activated at a time.\<close>

definition relays_inv :: "ilock_state upred" where [urel_defs]:
"relays_inv = (
  (R1 \<Rightarrow> \<not> R2 \<and> \<not> R4) \<or>
  (R2 \<Rightarrow> \<not> R1 \<and> \<not> R3 \<and> \<not> R4 \<and> \<not> R5) \<or>
  (R4 \<Rightarrow> \<not> R1 \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R5) \<or>
  (R3 \<Rightarrow> \<not> R2 \<and> \<not> R4 \<and> \<not> R5) \<or>
  (R5 \<Rightarrow> \<not> R2 \<and> \<not> R3 \<and> \<not> R4))"

lemma init_ilock_relays_inv:
"\<lbrace>true\<rbrace>init_ilock\<lbrace>relays_inv\<rbrace>\<^sub>u"
  unfolding init_ilock_def by hoare_auto

lemma set_relays_relays_inv:
"\<lbrace>ilock_type_inv \<and> relays_inv\<rbrace>set_relays\<lbrace>relays_inv\<rbrace>\<^sub>u"
  unfolding set_relays_def by hoare_auto

lemma reset_relays_relays_inv:
"\<lbrace>ilock_type_inv \<and> relays_inv\<rbrace>reset_relays\<lbrace>relays_inv\<rbrace>\<^sub>u"
  unfolding reset_relays_def by hoare_auto

lemma pos_switches_relays_inv:
"\<lbrace>ilock_type_inv \<and> relays_inv\<rbrace>pos_switches\<lbrace>relays_inv\<rbrace>\<^sub>u"
  unfolding pos_switches_def by hoare_auto

lemma set_signals_relays_inv:
"\<lbrace>ilock_type_inv \<and> relays_inv\<rbrace>set_signals\<lbrace>relays_inv\<rbrace>\<^sub>u"
  unfolding set_signals_def by hoare_auto

text {* First way of solving: using the lemmas about directly. *}

lemma "\<lbrace>ilock_type_inv \<and> relays_inv\<rbrace>ilock_cycle\<lbrace>relays_inv\<rbrace>\<^sub>u"
  apply (unfold ilock_cycle_def)
  apply (hoare_split)
  apply (simp_all add: hoare_r_weaken_pre(1) set_relays_type_inv set_relays_relays_inv 
                       reset_relays_relays_inv pos_switches_relays_inv set_signals_relays_inv 
                       reset_relays_type_inv pos_switches_type_inv)
done
    
text {* Second method: add the lemmas add additional Hoare rules (could also mark the theorems $hoare\_safe$) *}

lemma "\<lbrace>ilock_type_inv \<and> relays_inv\<rbrace>ilock_cycle\<lbrace>relays_inv\<rbrace>\<^sub>u"
  unfolding ilock_cycle_def
  by (hoare_split hr: set_relays_type_inv set_relays_relays_inv reset_relays_relays_inv 
                      pos_switches_relays_inv set_signals_relays_inv reset_relays_type_inv 
                      pos_switches_type_inv)

text {* Third method: direct proof *}                    
                    
lemma "\<lbrace>ilock_type_inv \<and> relays_inv\<rbrace>ilock_cycle\<lbrace>relays_inv\<rbrace>\<^sub>u"
  unfolding ilock_cycle_def set_signals_def pos_switches_def  set_relays_def reset_relays_def init_ilock_def
  by (hoare_auto)

subsection {* Proof Experiments *}

lemma "vector_from_list\<^sub>u_simp" [simp]:
"i \<in> {1..length l} \<Longrightarrow> (vector_from_list\<^sub>u l)[i]\<^sub>u = \<guillemotleft>l ! (i - 1)\<guillemotright>"
apply (pred_simp)
done

lemma lift_pre_subst_extract:
"\<lceil>P\<rceil>\<^sub><\<lbrakk>\<lceil>Q\<rceil>\<^sub></$v\<rbrakk> = \<lceil>P\<lbrakk>Q/&v\<rbrakk>\<rceil>\<^sub><"
apply (rel_simp)
done
end