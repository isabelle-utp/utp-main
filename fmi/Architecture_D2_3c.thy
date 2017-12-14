(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Architecture_D2_3c.thy                                               *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)

section {* Railways Architecture *}

theory Architecture_D2_3c
imports fmi
begin recall_syntax

subsection {* Preliminaries *}

subsubsection {* Track Segments *}

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

subsubsection {* Available Routes *}

definition "V1Q1 = (1::fmi2Integer)"
definition "V1Q2 = (2::fmi2Integer)"
definition "Q2V2 = (3::fmi2Integer)"
definition "V1Q3 = (4::fmi2Integer)"
definition "Q3V2 = (5::fmi2Integer)"

subsubsection {* Signal Encoding *}

definition "RED == False"
definition "GREEN == True"

fun signals :: "(bool \<times> bool \<times> bool) \<Rightarrow> fmi2Integer" where
"signals (s1, s2, s3) =
  (if s1 then 1 else 0) +
  (if s2 then 2 else 0) +
  (if s3 then 4 else 0)"

subsubsection {* Switch Encoding *}

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
  fmus_distinct: "distinct [train1, train2, merger, interlocking]" and
  FMI2COMP_def: "FMI2COMP = {train1, train2, merger, interlocking}"

overloading
  railways_FMUs \<equiv> "FMUs :: FMI2COMP list"
begin
  definition railways_FMUs :: "FMI2COMP list" where
  "railways_FMUs = [train1, train2, merger, interlocking]"
end

paragraph {* Proof Support *}

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
using fmus_distinct apply (auto)
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
  railways_inputs \<equiv> "inputs :: PORT list"
begin
  definition railways_inputs :: "PORT list" where
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
  railways_outputs \<equiv> "outputs :: PORT list"
begin
  definition railways_outputs :: "PORT list" where
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

overloading
  railways_initialValues \<equiv> "initialValues :: (PORT \<times> VAL) list"
begin
  definition railways_initialValues :: "(PORT \<times> VAL) list" where
  "railways_initialValues = [
    ((train1, $signals:{fmi2Integer}\<^sub>u), initialSignals),
    ((train1, $switches:{fmi2Integer}\<^sub>u), initialSwitches),
    ((train2, $signals:{fmi2Integer}\<^sub>u), initialSignals),
    ((train2, $switches:{fmi2Integer}\<^sub>u), initialSwitches),
    ((merger, $track_segment1:{fmi2Integer}\<^sub>u), initialTrack1),
    ((merger, $track_segment2:{fmi2Integer}\<^sub>u), initialTrack2),
    ((merger, $telecommand1:{fmi2Integer}\<^sub>u), undefined),
    ((merger, $telecommand2:{fmi2Integer}\<^sub>u), undefined),
    ((interlocking, $CDV:{fmi2Integer}\<^sub>u), undefined),
    ((interlocking, $TC:{fmi2Integer}\<^sub>u), undefined)]"
end

subsubsection {* Port Dependency Graph (\<open>pdg\<close>) *}

definition pdg :: "(PORT \<times> PORT) list" where
"pdg = [
  ((train1, $track_segment:{fmi2Integer}\<^sub>u), (merger, $track_segment1:{fmi2Integer}\<^sub>u)),
  ((train2, $track_segment:{fmi2Integer}\<^sub>u), (merger, $track_segment2:{fmi2Integer}\<^sub>u)),
  ((train1, $telecommand:{fmi2Integer}\<^sub>u), (merger, $telecommand1:{fmi2Integer}\<^sub>u)),
  ((train2, $telecommand:{fmi2Integer}\<^sub>u), (merger, $telecommand2:{fmi2Integer}\<^sub>u)),
  ((merger, $CDV:{fmi2Integer}\<^sub>u), (interlocking, $CDV:{fmi2Integer}\<^sub>u)),
  ((merger, $TC:{fmi2Integer}\<^sub>u), (interlocking, $TC:{fmi2Integer}\<^sub>u)),
  ((interlocking, $signals:{fmi2Integer}\<^sub>u), (train1, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $signals:{fmi2Integer}\<^sub>u), (train2, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $switches:{fmi2Integer}\<^sub>u), (train1, $switches:{fmi2Integer}\<^sub>u)),
  ((interlocking, $switches:{fmi2Integer}\<^sub>u), (train2, $switches:{fmi2Integer}\<^sub>u))
]"

subsubsection {* Internal Direct Dependencies (\<open>idd\<close>) *}

definition idd :: "(PORT \<times> PORT) list" where
"idd = [
  ((merger, $track_segment1:{fmi2Integer}\<^sub>u), (merger, $CDV:{fmi2Integer}\<^sub>u)),
  ((merger, $track_segment2:{fmi2Integer}\<^sub>u), (merger, $CDV:{fmi2Integer}\<^sub>u)),
  ((merger, $telecommand1:{fmi2Integer}\<^sub>u), (merger, $TC:{fmi2Integer}\<^sub>u)),
  ((merger, $telecommand2:{fmi2Integer}\<^sub>u), (merger, $TC:{fmi2Integer}\<^sub>u)),
  ((interlocking, $CDV:{fmi2Integer}\<^sub>u), (interlocking, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $CDV:{fmi2Integer}\<^sub>u), (interlocking, $switches:{fmi2Integer}\<^sub>u)),
  ((interlocking, $TC:{fmi2Integer}\<^sub>u), (interlocking, $signals:{fmi2Integer}\<^sub>u)),
  ((interlocking, $TC:{fmi2Integer}\<^sub>u), (interlocking, $switches:{fmi2Integer}\<^sub>u))
]"
end