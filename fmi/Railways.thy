(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Railways.thy                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Sep 2017 *)

section {* Railways Mechanisation *}

theory Railways
imports fmi String
begin

subsection {* Railways Constants *}

text {* Track Segments: CDV1-CDV11. *}

definition "CDV1 = (1::fmi2Integer)"
definition "CDV2 = (2::fmi2Integer)"
definition "CDV3 = (3::fmi2Integer)"
definition "CDV4 = (4::fmi2Integer)"
definition "CDV5 = (5::fmi2Integer)"
definition "CDV6 = (6::fmi2Integer)"
definition "CDV7 = (7::fmi2Integer)"
definition "CDV8 = (8::fmi2Integer)"
definition "CDV9 = (9::fmi2Integer)"
definition "CDV10 = (10::fmi2Integer)"
definition "CDV11 = (11::fmi2Integer)"

text {* Available Routes: V1Q1/V1Q2/Q2V2/V1Q3/Q3V2 *}

definition "V1Q1 = (1::fmi2Integer)"
definition "V1Q2 = (2::fmi2Integer)"
definition "Q2V2 = (3::fmi2Integer)"
definition "V1Q3 = (4::fmi2Integer)"
definition "Q3V2 = (5::fmi2Integer)"

subsection {* Signal Encoding *}

text {* TODO: Use `Isabelle Theories for Machine Words' by Jeremy Dawson. *}

definition "RED == False"
definition "GREEN == True"

fun signals :: "(bool \<times> bool \<times> bool) \<Rightarrow> fmi2Integer" where
"signals (s1, s2, s3) =
  (if s1 then 1 else 0) +
  (if s2 then 2 else 0) +
  (if s3 then 4 else 0)"

subsection {* Switch Encoding *}

text {* TODO: Use `Isabelle Theories for Machine Words' by Jeremy Dawson. *}

definition "STRAIGHT == False"
definition "DIVERGING == True"

fun switches :: "(bool \<times> bool \<times> bool \<times> bool \<times> bool) \<Rightarrow> fmi2Integer" where
"switches (sw1, sw2, sw3, sw4, sw5) =
  (if sw1 then 1 else 0) +
  (if sw2 then 2 else 0) +
  (if sw3 then 4 else 0) +
  (if sw4 then 8 else 0) +
  (if sw5 then 16 else 0)"

subsection {* Model Instantiation *}

subsubsection {* Railways FMUs *}

axiomatization
  train1 :: "FMI2COMP" and
  train2 :: "FMI2COMP" and
  merger :: "FMI2COMP" and
  interlocking :: "FMI2COMP" where
  fmus_distinct : "distinct [train1, train2, merger, interlocking]" and
  FMI2COMP_def : "FMI2COMP = {train1, train2, merger, interlocking}"

paragraph {* Proof Support *}

code_datatype "train1" "train2" "merger" "interlocking"

lemma fmu_simps [simp]:
"train1 \<noteq> train2"
"train1 \<noteq> merger"
"train1 \<noteq> interlocking"
"train2 \<noteq> train1"
"train2 \<noteq> merger"
"train2 \<noteq> interlocking"
"merger \<noteq> train1"
"merger \<noteq> train2"
"merger \<noteq> interlocking"
"interlocking \<noteq> train1"
"interlocking \<noteq> train2"
"interlocking \<noteq> merger"
using Railways.fmus_distinct apply (auto)
done

lemma fmu_code_simps [code]:
"equal_class.equal train1 train1 \<equiv> True"
"equal_class.equal train1 train2 \<equiv> False"
"equal_class.equal train1 merger \<equiv> False"
"equal_class.equal train1 interlocking \<equiv> False"
"equal_class.equal train2 train1 \<equiv> False"
"equal_class.equal train2 train2 \<equiv> True"
"equal_class.equal train2 merger \<equiv> False"
"equal_class.equal train2 interlocking \<equiv> False"
"equal_class.equal merger train1 \<equiv> False"
"equal_class.equal merger train2 \<equiv> False"
"equal_class.equal merger merger \<equiv> True"
"equal_class.equal merger interlocking \<equiv> False"
"equal_class.equal interlocking train1 \<equiv> False"
"equal_class.equal interlocking train2 \<equiv> False"
"equal_class.equal interlocking merger \<equiv> False"
"equal_class.equal interlocking interlocking \<equiv> True"
apply (unfold equal_FMI2COMP_def)
apply (simp_all only: fmu_simps refl)
done

subsubsection {* Parameters *}

overloading
  railways_parameters \<equiv> "parameters :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
  definition railways_parameters :: "(FMI2COMP \<times> VAR \<times> VAL) list" where
  "railways_parameters = [
    (train1, $max_speed:{fmi2Real}\<^sub>u, InjU (4.16::real)),
    (train2, $max_speed:{fmi2Real}\<^sub>u, InjU (4.16::real)),
    (train1, $fixed_route:{fmi2Integer}\<^sub>u, InjU V1Q2),
    (train2, $fixed_route:{fmi2Integer}\<^sub>u, InjU Q3V2)]"
end

subsubsection {* Inputs and Outputs *}

overloading
  railways_inputs \<equiv> "inputs :: (FMI2COMP \<times> VAR) list"
begin
  definition railways_inputs :: "(FMI2COMP \<times> VAR) list" where
  "railways_inputs = [
    (train1, $signals:{fmi2Integer}\<^sub>u),
    (train1, $switches:{fmi2Integer}\<^sub>u),
    (train2, $signals:{fmi2Integer}\<^sub>u),
    (train2, $switches:{fmi2Integer}\<^sub>u),
    (merger, $track_segment1:{fmi2Integer}\<^sub>u),
    (merger, $track_segment2:{fmi2Integer}\<^sub>u),
    (merger, $telecommand1:{fmi2Integer}\<^sub>u),
    (merger, $telecommand2:{fmi2Integer}\<^sub>u),
    (interlocking, $CDV:{fmi2Integer}\<^sub>u),
    (interlocking, $TC:{fmi2Integer}\<^sub>u)]"
end

overloading
  railways_outputs \<equiv> "outputs :: (FMI2COMP \<times> VAR) list"
begin
  definition railways_outputs :: "(FMI2COMP \<times> VAR) list" where
  "railways_outputs = [
    (train1, $track_segment:{fmi2Integer}\<^sub>u),
    (train1, $telecommand:{fmi2Integer}\<^sub>u),
    (train2, $track_segment:{fmi2Integer}\<^sub>u),
    (train2, $telecommand:{fmi2Integer}\<^sub>u),
    (merger, $CDV:{fmi2Integer}\<^sub>u),
    (merger, $TC:{fmi2Integer}\<^sub>u),
    (merger, $collision:{fmi2Boolean}\<^sub>u),
    (merger, $derailment:{fmi2Boolean}\<^sub>u),
    (interlocking, $signals:{fmi2Integer}\<^sub>u),
    (interlocking, $switches:{fmi2Integer}\<^sub>u)]"
end

subsubsection {* Initial Values *}

text {* The following constants have to be defined as appropriate. *}

definition "initialSignals = InjU (signals (RED, RED, RED))"
definition "initialSwitches =
  InjU (switches (STRAIGHT, STRAIGHT, STRAIGHT, STRAIGHT, STRAIGHT))"
definition "initialTrack1 = InjU CDV3"
definition "initialTrack2 = InjU CDV2"

text {* What about the initial values for telecommand, CDV and TC? *}

overloading
  railways_initialValues \<equiv> "initialValues :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
  definition railways_initialValues :: "(FMI2COMP \<times> VAR \<times> VAL) list" where
  "railways_initialValues = [
    (train1, $signals:{fmi2Integer}\<^sub>u, initialSignals),
    (train1, $switches:{fmi2Integer}\<^sub>u, initialSwitches),
    (train2, $signals:{fmi2Integer}\<^sub>u, initialSignals),
    (train2, $switches:{fmi2Integer}\<^sub>u, initialSwitches),
    (merger, $track_segment1:{fmi2Integer}\<^sub>u, initialTrack1),
    (merger, $track_segment2:{fmi2Integer}\<^sub>u, initialTrack2),
    (merger, $telecommand1:{fmi2Integer}\<^sub>u, undefined),
    (merger, $telecommand2:{fmi2Integer}\<^sub>u, undefined),
    (interlocking, $CDV:{fmi2Integer}\<^sub>u, undefined),
    (interlocking, $TC:{fmi2Integer}\<^sub>u, undefined)]"
end

subsubsection {* Port Dependency Graph (\<open>pdg\<close>) *}

definition pdg :: "port relation" where
"pdg = {
  ((train1, $track_segment:{fmi2Integer}\<^sub>u), (merger, $track_segment1:{fmi2Integer}\<^sub>u)),
  ((train2, $track_segment:{fmi2Integer}\<^sub>u), (merger, $track_segment2:{fmi2Integer}\<^sub>u)),
  ((train1, $telecommand:{fmi2Integer}\<^sub>u), (merger, $telecommand:{fmi2Integer}\<^sub>u)),
  ((train2, $telecommand:{fmi2Integer}\<^sub>u), (merger, $telecommand:{fmi2Integer}\<^sub>u)),
  ((merger, $CDV:{fmi2Integer}\<^sub>u), (interlocking, $CDV:{fmi2Integer}\<^sub>u)),
  ((merger, $TC:{fmi2Integer}\<^sub>u), (interlocking, $TC:{fmi2Integer}\<^sub>u)),
  ((interlocking, $signals:{fmi2Integer}\<^sub>u), (train1, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $signals:{fmi2Integer}\<^sub>u), (train2, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $switches:{fmi2Integer}\<^sub>u), (train1, $switches:{fmi2Integer}\<^sub>u)),
  ((interlocking, $switches:{fmi2Integer}\<^sub>u), (train2, $switches:{fmi2Integer}\<^sub>u))
}"

subsubsection {* Internal Direct Dependencies (\<open>idd\<close>) *}

definition idd :: "port relation" where
"idd = {
  (* The two below are not direct dependencies due to integrators in the CTL. *)
  (* ((train1, $switches:{fmi2Integer}\<^sub>u), (train1, $track_segment:{fmi2Integer}\<^sub>u)), *)
  (* ((train2, $switches:{fmi2Integer}\<^sub>u), (train1, $track_segment:{fmi2Integer}\<^sub>u)), *)
  ((merger, $track_segment1:{fmi2Integer}\<^sub>u), (merger, $CDV:{fmi2Integer}\<^sub>u)),
  ((merger, $track_segment2:{fmi2Integer}\<^sub>u), (merger, $CDV:{fmi2Integer}\<^sub>u)),
  ((merger, $telecommand:{fmi2Integer}\<^sub>u), (merger, $TC:{fmi2Integer}\<^sub>u)),
  ((merger, $telecommand:{fmi2Integer}\<^sub>u), (merger, $TC:{fmi2Integer}\<^sub>u)),
  ((interlocking, $CDV:{fmi2Integer}\<^sub>u), (interlocking, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $CDV:{fmi2Integer}\<^sub>u), (interlocking, $switches:{fmi2Integer}\<^sub>u)),
  ((interlocking, $TC:{fmi2Integer}\<^sub>u), (interlocking, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $TC:{fmi2Integer}\<^sub>u), (interlocking, $switches:{fmi2Integer}\<^sub>u))
}"

(*<*)
(* Content used for the CoSim-CPS 2017 paper. *)

consts dummy :: "'a" ("\<dots>")

experiment
begin
definition pdg :: "port relation" where
"pdg = {
  (* External Dependencies *)
  ((train1, $track_segment:{int}\<^sub>u), (merger, $track_segment1:{int}\<^sub>u)),
  ((train2, $track_segment:{int}\<^sub>u), (merger, $track_segment2:{int}\<^sub>u)), \<dots>,
  (* Internal Dependencies *)
  ((merger, $track_segment1:{int}\<^sub>u), (merger, $CDV:{int}\<^sub>u)),
  ((merger, $track_segment2:{int}\<^sub>u), (merger, $CDV:{int}\<^sub>u)), \<dots>
}"
end
(*>*)

subsection {* Proof of Properties *}

subsubsection {* Port Conformance Check *}

inductive conformant :: "port relation \<Rightarrow> bool" where
"conformant {}" |
"type (snd p1) = type (snd p2) \<Longrightarrow>
  conformant S \<Longrightarrow> conformant (insert (p1, p2)  S)"

declare conformant.intros [intro!]

lemma pdg_conformant:
"conformant pdg" unfolding pdg_def by (auto)

lemma idd_conformant:
"conformant idd" unfolding idd_def by (auto)

subsubsection {* Absence of Algebraic Loops *}

text {* Needed for evaluation of @{term "(STR s1) = (STR s2)"} terms. *}

declare equal_literal.rep_eq [code del]

text {* We next prove via code evaluation that there are no algebraic loops. *}

lemma "acyclic (pdg \<union> idd)"
profile (eval)
done

subsection {* Proof Experiments *}

lemma acyclic_witnessI:
"(\<exists>s. r \<subseteq> s \<and> s O r \<subseteq> s \<and> irrefl s) \<Longrightarrow> acyclic r"
apply (clarsimp)
apply (subgoal_tac "r\<^sup>+ \<subseteq> s")
apply (meson acyclic_def irrefl_def subsetCE)
apply (erule trancl_Int_subset)
apply (auto)
done
end