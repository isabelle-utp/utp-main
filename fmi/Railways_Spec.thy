(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Railways_Spec.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 19 Oct 2017 *)

section {* Railways Specification *}

theory Railways_Spec
imports Vector Topology utp_hoare_ext
begin recall_syntax

consts dots :: "'a" ("\<dots>")

declare [[syntax_ambiguity_warning=false]]

(* declare atLeastAtMost_iff [simp del] *)

definition front :: "'a list \<Rightarrow> 'a list" where
"front l = rev (tl (rev l))"

abbreviation middle :: "'a list \<Rightarrow> 'a list" where
"middle l \<equiv> front (tl l)"

subsection {* Isabelle/UTP Laws *}

lemma uimp_uconjI:
"`P \<Rightarrow> Q` \<Longrightarrow>
 `P \<Rightarrow> R` \<Longrightarrow>
 `P \<Rightarrow> Q \<and> R`"
apply (pred_auto)
done

lemma uconjD1:
"`P \<Rightarrow> R` \<Longrightarrow> `P \<and> Q \<Rightarrow> R`"
apply (pred_auto)
done

lemma uconjD2:
"`Q \<Rightarrow> R` \<Longrightarrow> `P \<and> Q \<Rightarrow> R`"
apply (pred_auto)
done

lemma exportation:
"`P \<and> Q \<Rightarrow> R` = `P \<Rightarrow> Q \<Rightarrow> R`"
apply (pred_auto)
done

method ustrip_tac =
  (rule uimp_uconjI; ustrip_tac)?

subsection {* Centralised FMU State *}

type_synonym TIME = "nat"

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
  (* Simulation Time *)
  time :: "TIME"

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
    time\<^sub>v r,
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
    time\<^sub>v r, time\<^sub>v r',
    more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsection {* Type Invariant *}

definition railways_type_inv :: "railways_state upred" where [upred_defs]:
"railways_type_inv = (
  &current_track\<^sub>1 \<in>\<^sub>u \<guillemotleft>{-1..11}\<guillemotright> \<and> #\<^sub>u(&telecommand\<^sub>1) =\<^sub>u 4 \<and>
  &current_track\<^sub>2 \<in>\<^sub>u \<guillemotleft>{-1..11}\<guillemotright> \<and> #\<^sub>u(&telecommand\<^sub>2) =\<^sub>u 4 \<and>
  #\<^sub>u(&cdv) =\<^sub>u 11 \<and> #\<^sub>u(&tc) =\<^sub>u 4 \<and>
  #\<^sub>u(&relays) =\<^sub>u 5 \<and> #\<^sub>u(&signals) =\<^sub>u 3 \<and> #\<^sub>u(&switches) =\<^sub>u 5)"

subsection {* Safety Invariant *}

definition present\<^sub>1 :: "railways_state upred" where [upred_defs]:
"present\<^sub>1 = (&current_track\<^sub>1 \<noteq>\<^sub>u 0)"

definition present\<^sub>2 :: "railways_state upred" where [upred_defs]:
"present\<^sub>2 = (&current_track\<^sub>2 \<noteq>\<^sub>u 0)"

definition derailed\<^sub>1 :: "railways_state upred" where [upred_defs]:
"derailed\<^sub>1 = (&current_track\<^sub>1 =\<^sub>u -1)"

definition derailed\<^sub>2 :: "railways_state upred" where [upred_defs]:
"derailed\<^sub>2 = (&current_track\<^sub>2 =\<^sub>u -1)"

definition safety_req :: "railways_state upred" where [upred_defs]:
"safety_req =
  (\<not> derailed\<^sub>1 \<and> \<not> derailed\<^sub>2 \<and>
  (present\<^sub>1 \<and> present\<^sub>2 \<Rightarrow> &current_track\<^sub>1 \<noteq>\<^sub>u &current_track\<^sub>2))"

subsection {* Relays Invariant *}

text \<open>Ensures that at most one relay can be activated at a time.\<close>

definition relays_excl_inv :: "railways_state upred" where [upred_defs]:
"relays_excl_inv = (
  (#\<^sub>u(&relays) =\<^sub>u 5) \<and>
  (R1 \<Rightarrow> \<not> R2 \<and> \<not> R4) \<and>
  (R2 \<Rightarrow> \<not> R1 \<and> \<not> R3 \<and> \<not> R4 \<and> \<not> R5) \<and>
  (R3 \<Rightarrow> \<not> R2 \<and> \<not> R4 \<and> \<not> R5) \<and>
  (R4 \<Rightarrow> \<not> R1 \<and> \<not> R2 \<and> \<not> R3 \<and> \<not> R5) \<and>
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

lemma relays_excl_inv_split_alt:
"`relays_excl_inv \<and> P \<Rightarrow> Q` = `\<^bold>\<forall> v\<in>\<guillemotleft>valid_relay_states\<guillemotright> \<bullet> (P \<Rightarrow> Q)\<lbrakk>\<guillemotleft>v\<guillemotright> / &relays\<rbrakk>`"
apply (fold relays_excl_inv_split)
apply (rule exportation)
done

lemma in_nat_set_1_to_5:
"x \<in> {(1::nat)..5} \<longleftrightarrow> x \<in> {1, 2, 3, 4, 5}"
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

subsection {* Train Scenarios *}

text {*
  Train scenarios configure the routes for the two trains passing through the
  interlocking. There are several additional assumptions that need to hold for
  routes pairs to be valid, such as the routes must be distinct and their first
  and last track must not (mutually) overlap. We encapsulate those assumptions
  by way of a locale.
*}

locale train_scenario =
  fixes route\<^sub>1 :: "nat"
  fixes route\<^sub>2 :: "nat"
  assumes route1_in_range: "route\<^sub>1 \<in> ROUTES"
  assumes route2_in_range: "route\<^sub>2 \<in> ROUTES"
  assumes routes_distinct: "route\<^sub>1 \<noteq> route\<^sub>2"
  assumes routes_excl:
    "hd (routes!route\<^sub>1) \<noteq> hd (routes!route\<^sub>2)"
    "hd (routes!route\<^sub>1) \<noteq> last (routes!route\<^sub>2)"
    "last (routes!route\<^sub>1) \<noteq> hd (routes!route\<^sub>2)"
    "last (routes!route\<^sub>1) \<noteq> last (routes!route\<^sub>2)"
begin

text {* Initial and final track, as well as travel direction can be derived. *}

definition initial_track\<^sub>1 :: "int" where
[urel_defs]: "initial_track\<^sub>1 = hd (routes!route\<^sub>1)"

definition initial_track\<^sub>2 :: "int" where
[urel_defs]: "initial_track\<^sub>2 = hd (routes!route\<^sub>2)"

definition final_track\<^sub>1 :: "int" where
[urel_defs]: "final_track\<^sub>1 = last (routes!route\<^sub>1)"

definition final_track\<^sub>2 :: "int" where
[urel_defs]: "final_track\<^sub>2 = last (routes!route\<^sub>2)"

definition direction\<^sub>1 :: "direction" where
[urel_defs]: "direction\<^sub>1 = (directions!route\<^sub>1)"

definition direction\<^sub>2 :: "direction" where
[urel_defs]: "direction\<^sub>2 = (directions!route\<^sub>2)"

paragraph {* Useful lemmas *}

lemma route1_cases:
"(\<And>route1. route1 \<in> ROUTES \<Longrightarrow> P route1) \<Longrightarrow> P route\<^sub>1"
using route1_in_range by (auto)

lemma route2_cases:
"(\<And>route2. route2 \<in> ROUTES \<Longrightarrow> P route2) \<Longrightarrow> P route\<^sub>2"
using route2_in_range by (auto)

lemma route_cases:
"(\<And>route1 route2.
  route1 \<in> ROUTES \<Longrightarrow>
  route2 \<in> ROUTES \<Longrightarrow>
  route1 \<noteq> route2 \<Longrightarrow>
  hd (routes!route1) \<noteq> hd (routes!route2) \<Longrightarrow>
  hd (routes!route1) \<noteq> last (routes!route2) \<Longrightarrow>
  last (routes!route1) \<noteq> hd (routes!route2) \<Longrightarrow>
  last (routes!route1) \<noteq> last (routes!route2) \<Longrightarrow>
  P route1 route2) \<Longrightarrow> P route\<^sub>1 route\<^sub>2"
  by (metis route1_in_range route2_in_range routes_excl)
end

text {*
  We next define the global train scenario that we consider in proofs. Rather
  than assuming particular routes, we keep the route configuration abstract by
  using indefinite description (Hilbert's epsilon). Our approach effectively
  allows us to prove properties of the cosimulation, such as global and safety
  invariants for \emph{all} possible train scenarios.
*}

definition route\<^sub>1 :: "nat" where
"route\<^sub>1 = fst (SOME (route\<^sub>1, route\<^sub>2). train_scenario route\<^sub>1 route\<^sub>2)"

definition route\<^sub>2 :: "nat" where
"route\<^sub>2 = snd (SOME (route\<^sub>1, route\<^sub>2). train_scenario route\<^sub>1 route\<^sub>2)"

lemma train_scenario_witness:
"train_scenario V1Q1 Q2V2"
apply (unfold_locales)
apply (simp_all add: routes_def)
done

lemma train_scenario:
"train_scenario route\<^sub>1 route\<^sub>2"
apply (unfold route\<^sub>1_def route\<^sub>2_def)
apply (rule someI2_ex)
apply (rule_tac x = "(V1Q1, Q2V2)" in exI)
apply (simp del: One_nat_def)
apply (rule train_scenario_witness)
apply (clarsimp)
done

interpretation train_scenario "route\<^sub>1" "route\<^sub>2"
apply (rule train_scenario)
done

subsection {* Train Model *}

definition MustWait :: "bool vector \<Rightarrow> int \<Rightarrow> bool" where
"MustWait sig track \<longleftrightarrow>
  (track = 1 \<and> sig\<^bold>[1\<^bold>]) \<or> (track = 2 \<and> sig\<^bold>[2\<^bold>]) \<or> (track = 3 \<and> sig\<^bold>[3\<^bold>])"

fun MoveTrain :: "int \<times> direction \<times> (bool vector) \<times> (switch vector) \<Rightarrow> int" where
"MoveTrain (track, dir, sig, sw) =
  (if track =  0 then  0 else
  (if track = -1 then -1 else
  (if MustWait sig track then track
   else (case dir of
    QtoV \<Rightarrow> NextTrackQV sw track |
    VtoQ \<Rightarrow> NextTrackVQ sw track))))"

syntax "_MoveTrack\<^sub>u" ::
  "(int \<times> direction \<times> (bool vector) \<times> (switch vector) \<Rightarrow> int, '\<alpha>) uexpr"
  ("MoveTrain\<^sub>u")

translations "MoveTrain\<^sub>u" \<rightleftharpoons> "\<guillemotleft>CONST MoveTrain\<guillemotright>"

definition Train1 :: "TIME \<Rightarrow> railways_state hrel" where
"Train1 \<epsilon> = (
  ($current_track\<^sub>1\<acute> =\<^sub>u $current_track\<^sub>1 \<or>
   $current_track\<^sub>1\<acute> =\<^sub>u MoveTrain\<^sub>u($current_track\<^sub>1, \<guillemotleft>direction\<^sub>1\<guillemotright>, $signals, $switches)\<^sub>a)
  \<and> $telecommand\<^sub>1\<acute> =\<^sub>u \<dots> \<and> $time\<acute> \<le>\<^sub>u $time + \<guillemotleft>\<epsilon>\<guillemotright>)"

definition Train2 :: "TIME \<Rightarrow> railways_state hrel" where
"Train2 \<epsilon> = (
  ($current_track\<^sub>2\<acute> =\<^sub>u $current_track\<^sub>2 \<or>
   $current_track\<^sub>2\<acute> =\<^sub>u MoveTrain\<^sub>u($current_track\<^sub>2, \<guillemotleft>direction\<^sub>2\<guillemotright>, $signals, $switches)\<^sub>a)
  \<and> $telecommand\<^sub>2\<acute> =\<^sub>u \<dots> \<and> $time\<acute> \<le>\<^sub>u $time + \<guillemotleft>\<epsilon>\<guillemotright>)"

subsection {* Train Invariant *}

definition train1_inv :: "railways_state upred" where
[urel_defs]: "train1_inv = (
  &current_track\<^sub>1 =\<^sub>u \<guillemotleft>initial_track\<^sub>1\<guillemotright> \<or>
  (&relays[route\<^sub>1]\<^sub>u \<and> &current_track\<^sub>1 \<in>\<^sub>u \<guillemotleft>set (routes!route\<^sub>1)\<guillemotright>) \<or>
  &current_track\<^sub>1 =\<^sub>u \<guillemotleft>final_track\<^sub>1\<guillemotright> \<or>
  &current_track\<^sub>1 =\<^sub>u 0)"

definition train2_inv :: "railways_state upred" where
[urel_defs]: "train2_inv = (
  &current_track\<^sub>2 =\<^sub>u \<guillemotleft>initial_track\<^sub>2\<guillemotright> \<or>
  (&relays[route\<^sub>2]\<^sub>u \<and> &current_track\<^sub>2 \<in>\<^sub>u \<guillemotleft>set (routes!route\<^sub>2)\<guillemotright>) \<or>
  &current_track\<^sub>2 =\<^sub>u \<guillemotleft>final_track\<^sub>2\<guillemotright> \<or>
  &current_track\<^sub>2 =\<^sub>u 0)"

subsection {* Proof of Safety *}

text {* Proof that the train invariants imply safety. *}

context train_scenario
begin
lemma route1_non_empty:
"routes!route\<^sub>1 \<noteq> []"
apply (rule route1_cases)
apply (safe; simp add: routes_def)
done

lemma route2_non_empty:
"routes!route\<^sub>2 \<noteq> []"
apply (rule route2_cases)
apply (safe; simp add: routes_def)
done
end

lemma mem_set_split:
"l \<noteq> [] \<Longrightarrow> x \<in> set l \<longleftrightarrow> (x = hd l \<or> x \<in> set (tl l))"
apply (induction l)
apply (simp_all)
done

lemma at_route_simps [simp]:
"(vector_from_list [a, b, c, d, e])\<^bold>[route\<^sub>1\<^bold>] = [a, b, c, d, e]!(route\<^sub>1 - 1)"
"(vector_from_list [a, b, c, d, e])\<^bold>[route\<^sub>2\<^bold>] = [a, b, c, d, e]!(route\<^sub>2 - 1)"
apply (rule route1_cases)
apply (safe; simp)
apply (rule route2_cases)
apply (safe; simp)
done

lemma hd_route1_not_in_set_route2:
"hd (routes!route\<^sub>1) \<notin> set (routes!route\<^sub>2)"
apply (subst mem_set_split)
apply (rule route2_non_empty)
apply (safe; erule contrapos_pp; simp)
apply (rule routes_excl(1))
apply (rule route_cases)
apply (safe; simp add: routes_def)
done

lemma hd_route2_not_in_set_route1:
"hd (routes!route\<^sub>2) \<notin> set (routes!route\<^sub>1)"
apply (subst mem_set_split)
apply (rule route1_non_empty)
apply (safe; erule contrapos_pp; simp)
apply (subst eq_commute)
apply (rule routes_excl(1))
apply (rule route_cases)
apply (safe; simp add: routes_def)
done

lemma last_route1_not_in_set_route2:
"last (routes!route\<^sub>1) \<notin> set (routes!route\<^sub>2)"
apply (subst mem_set_split)
apply (rule route2_non_empty)
apply (safe; erule contrapos_pp; simp)
apply (rule routes_excl(3))
apply (rule route_cases)
apply (safe; simp add: routes_def)
done

lemma last_route2_not_in_set_route1:
"last (routes!route\<^sub>2) \<notin> set (routes!route\<^sub>1)"
apply (subst mem_set_split)
apply (rule route1_non_empty)
apply (safe; erule contrapos_pp; simp)
apply (subst eq_commute)
apply (rule routes_excl(2))
apply (rule route_cases)
apply (safe; simp add: routes_def)
done

lemma safety_req_lemma1:
"`train1_inv \<Rightarrow> \<not> derailed\<^sub>1`"
apply (rel_simp)
apply (rule route1_cases)
apply (safe; simp add: routes_def)
done

lemma safety_req_lemma2:
"`train2_inv \<Rightarrow> \<not> derailed\<^sub>2`"
apply (rel_simp)
apply (rule route2_cases)
apply (safe; simp add: routes_def)
done

lemma safety_req_lemma3:
"`relays_excl_inv \<and> train1_inv \<and> train2_inv \<Rightarrow>
  (present\<^sub>1 \<and> present\<^sub>2 \<Rightarrow> &current_track\<^sub>1 \<noteq>\<^sub>u &current_track\<^sub>2)`"
apply (subst relays_excl_inv_split_alt)
apply (rel_simp)
apply (rename_tac rs)
apply (safe)
-- {* Subgoal 1 *}
using routes_excl(1)
apply (auto) [1]
-- {* Subgoal 2 *}
using hd_route1_not_in_set_route2
apply (auto) [1]
-- {* Subgoal 3 *}
using routes_excl(2)
apply (auto) [1]
-- {* Subgoal 4 *}
using hd_route2_not_in_set_route1
apply (auto) [1]
-- {* Subgoal 5 *}
using routes_excl(3)
apply (auto) [1]
-- {* Subgoal 6 *}
apply (subgoal_tac "set (routes!route\<^sub>1) \<inter> set (routes!route\<^sub>2) = {}")
-- {* Subgoal 5.1 *}
apply (blast)
-- {* Subgoal 5.2 *}
apply (erule routes_disjoint)
apply (assumption)
apply (assumption)
using in_nat_set_1_to_5 route1_in_range apply (blast)
using in_nat_set_1_to_5 route2_in_range apply (blast)
using routes_distinct apply (blast)
-- {* Subgoal 7 *}
using last_route2_not_in_set_route1
apply (auto) [1]
-- {* Subgoal 8 *}
using last_route1_not_in_set_route2
apply (auto) [1]
-- {* Subgoal 9 *}
using routes_excl(4)
apply (auto) [1]
done

lemma safety_req_holds:
"`relays_excl_inv \<and> train1_inv \<and> train2_inv \<Rightarrow> safety_req`"
apply (unfold safety_req_def)
apply (ustrip_tac)
-- {* Subgoal 1 *}
apply (rule uconjD2; rule uconjD1)
apply (rule safety_req_lemma1)
-- {* Subgoal 2 *}
apply (rule uconjD2; rule uconjD2)
apply (rule safety_req_lemma2)
-- {* Subgoal 3 *}
apply (rule safety_req_lemma3)
done

subsection {* Merger Model *}

definition MergeCDV :: "int \<Rightarrow> (bool vector) \<Rightarrow> (bool vector)" where
"MergeCDV i v =
  (if i = 0 \<or> i = -1 then v else
  (if i \<in> {1..13} then v\<^bold>[nat i\<^bold>] \<hookleftarrow> False else undefined))"

fun MakeCDV :: "int \<times> int \<Rightarrow> (bool vector)" where
"MakeCDV (i, j) = (MergeCDV i (MergeCDV j (mk_vector 13 True)))"

syntax "_MakeCDV" ::
  "(int \<times> int \<Rightarrow> (bool vector), railways_state) uexpr" ("MakeCDV\<^sub>u")

translations "MakeCDV\<^sub>u" \<rightleftharpoons> "\<guillemotleft>CONST MakeCDV\<guillemotright>"

definition Merger :: "railways_state hrel" where
"Merger = ($cdv\<acute> =\<^sub>u MakeCDV\<^sub>u($current_track\<^sub>1, $current_track\<^sub>2)\<^sub>a \<and> $tc\<acute> =\<^sub>u \<dots>)"

subsection {* Proof Experiments *}

lemma udisj_hoare:
"\<lbrace>p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p\<rbrace>T\<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p\<rbrace>S \<or> T\<lbrace>q\<rbrace>\<^sub>u"
apply (rel_auto)
done

declare MoveTrain.simps [simp del]

definition relays_set_inv [upred_defs]:
"relays_set_inv =
  (&current_track\<^sub>1 \<in>\<^sub>u \<guillemotleft>set (middle (routes!route\<^sub>1))\<guillemotright> \<Rightarrow> &relays[route\<^sub>1]\<^sub>u)"

method route1_cases_tac =
  ((erule rev_mp)+, rule route1_cases,
    (safe; (simp add: routes_def front_def)?))

lemma in_set_list_split3:
"l \<noteq> [] \<Longrightarrow> x \<in> set l = (x = hd l \<or> x \<in> set (middle l) \<or> x = last l)"
apply (unfold front_def)
apply (metis (no_types, lifting)
  Nil_is_rev_conv hd_rev last_tl mem_set_split set_rev tl_Nil)
done

lemma "\<lbrace>train1_inv\<rbrace>Train1 \<epsilon>\<lbrace>relays_set_inv \<Rightarrow> train1_inv\<rbrace>\<^sub>u"
apply (unfold Train1_def)
apply (unfold train1_inv_def)
apply (rel_simp)
apply (safe; clarsimp; thin_tac "telecommand\<^sub>1\<^sub>v' = _")
apply (meson in_set_list_split3 route1_non_empty)
-- {* A few more days work to do here to prove this invariant! *}
oops

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