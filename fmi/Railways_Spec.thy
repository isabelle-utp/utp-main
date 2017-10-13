(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Railways_Spec.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 22 Sep 2017 *)

section {* Railways Specification *}

theory Railways_Spec
imports Vector Topology utp_hoare_ext
begin recall_syntax

subsection {* Centralised FMU State *}

alphabet railways_state =
  (* Train FMUs *)
  current_track\<^sub>1 :: "int"
  current_track\<^sub>2 :: "int"
  telecommand\<^sub>1 :: "bool vector"
  telecommand\<^sub>2 :: "bool vector"
  (* Merger FMU *)
  cdv :: "bool vector"
  tc :: "bool vector"
  (* Interlocking FMU *)
  relays :: "bool vector"
  signals :: "bool vector"
  switches :: "switch vector"

text \<open>Convenience syntax for indexed access of @{const cdv}.\<close>

abbreviation CDV :: "nat \<Rightarrow> (bool, railways_state) uexpr" ("CDV[_]") where
"CDV[i] \<equiv> &cdv[i]\<^sub>u"

text \<open>Convenience syntax for indexed access of @{const tc}.\<close>

abbreviation TC :: "nat \<Rightarrow> (bool, railways_state) uexpr" ("TC[_]") where
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

text \<open>Interpretations for the @{type railways_state} alphabet type.\<close>

interpretation railways_state_interp1:
  lens_interp "\<lambda>r. (
    current_track\<^sub>1\<^sub>v r,
    current_track\<^sub>2\<^sub>v r,
    telecommand\<^sub>1\<^sub>v r,
    telecommand\<^sub>2\<^sub>v r,
    cdv\<^sub>v r,
    tc\<^sub>v r,
    relays\<^sub>v r,
    signals\<^sub>v r,
    switches\<^sub>v r,
    more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation ilock_var_interp2:
  lens_interp "\<lambda>(r, r'). (
    current_track\<^sub>1\<^sub>v r, current_track\<^sub>1\<^sub>v r',
    current_track\<^sub>2\<^sub>v r, current_track\<^sub>2\<^sub>v r',
    telecommand\<^sub>1\<^sub>v r, telecommand\<^sub>1\<^sub>v r',
    telecommand\<^sub>2\<^sub>v r, telecommand\<^sub>2\<^sub>v r',
    cdv\<^sub>v r, cdv\<^sub>v r',
    tc\<^sub>v r, tc\<^sub>v r',
    relays\<^sub>v r, relays\<^sub>v r',
    signals\<^sub>v r, signals\<^sub>v r',
    switches\<^sub>v r, switches\<^sub>v r',
    more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsection {* Type Invariant *}

definition railways_type_inv :: "railways_state upred" where [upred_defs]:
"railways_type_inv = (
  &current_track\<^sub>1 \<in>\<^sub>u \<guillemotleft>{-1..11}\<guillemotright> \<and>
  &current_track\<^sub>2 \<in>\<^sub>u \<guillemotleft>{-1..11}\<guillemotright> \<and>
  #\<^sub>u(&telecommand\<^sub>1) =\<^sub>u 4 \<and>
  #\<^sub>u(&telecommand\<^sub>2) =\<^sub>u 4 \<and>
  #\<^sub>u(&cdv) =\<^sub>u 11 \<and>
  #\<^sub>u(&tc) =\<^sub>u 4 \<and>
  #\<^sub>u(&relays) =\<^sub>u 5 \<and>
  #\<^sub>u(&signals) =\<^sub>u 3 \<and>
  #\<^sub>u(&switches) =\<^sub>u 5)"

subsection {* Safety Invariant *}

definition present\<^sub>1 :: "railways_state upred" where [upred_defs]:
"present\<^sub>1 = (&current_track\<^sub>1 \<noteq>\<^sub>u 0)"

definition present\<^sub>2 :: "railways_state upred" where [upred_defs]:
"present\<^sub>2 = (&current_track\<^sub>2 \<noteq>\<^sub>u 0)"

definition derailed\<^sub>1 :: "railways_state upred" where [upred_defs]:
"derailed\<^sub>1 = (&current_track\<^sub>1 =\<^sub>u -1)"

definition derailed\<^sub>2 :: "railways_state upred" where [upred_defs]:
"derailed\<^sub>2 = (&current_track\<^sub>2 =\<^sub>u -1)"

definition safety_inv :: "railways_state upred" where [upred_defs]:
"safety_inv = (\<not> derailed\<^sub>1 \<and> \<not> derailed\<^sub>2 \<and> 
  (present\<^sub>1 \<and> present\<^sub>2 \<Rightarrow> &current_track\<^sub>1 \<noteq>\<^sub>u &current_track\<^sub>2))"

subsection {* Relays Invariant *}

text \<open>Ensures that at most one relay can be activated at a time.\<close>

definition relays_excl_inv :: "railways_state upred" where [upred_defs]:
"relays_excl_inv = (
  (#\<^sub>u(&relays) =\<^sub>u 5) \<and>
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

subsection {* Lemmas *}

lemma in_nat_set_1_to_5:
"x \<in> {(1::nat)..5} = (x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5)"
apply (safe; clarsimp)
done

lemma routes_disjoint:
"rs \<in> valid_relay_states \<Longrightarrow>
 rs\<^bold>[i\<^bold>] \<Longrightarrow>
 rs\<^bold>[j\<^bold>] \<Longrightarrow>
 i \<in> {1..5} \<Longrightarrow>
 j \<in> {1..5} \<Longrightarrow>
 i \<noteq> j \<Longrightarrow> set (routes ! i) \<inter> set (routes ! j) = {}"
apply (unfold valid_relay_states_def)
apply (safe; thin_tac "rs = vector_from_list _")
apply (unfold in_nat_set_1_to_5)
apply (safe; simp; unfold routes_def; auto)+
done

subsection {* Proof Experiments *}
(*
declare atLeastAtMost_iff [simp del]

lemma [simp]:
"((i::'a::order) \<in> {n..n}) = (i = n)"
apply (auto)
done

lemma [simp]:
"n \<le> m \<Longrightarrow> i \<in> {n..m} = (i = n \<or> i \<in> {Suc n..m})"
apply (unfold atLeastAtMost_iff)
apply (auto)
done
*)
end