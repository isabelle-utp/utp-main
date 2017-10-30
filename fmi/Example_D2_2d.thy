(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Example_D2_2d.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Sep 2017 *)

section {* FMI Instantiation for the Example in D2.2d *}

theory "Example_D2_2d"
imports fmi
begin

text {*
  Instead of using integer numbers to name variables, I am using symbolic names
  @{text x}, @{text y} and @{text z} below. Perhaps more meaningful names can
  be chosen; for this, I would need to understand better what kind of system
  the example in D2.2d is trying to model.
*}

subsection {* FMU Components *}

axiomatization
  pdsgfmu1 :: "FMI2COMP" and
  pdsgfmu2 :: "FMI2COMP" and
  samplerfmu :: "FMI2COMP" and
  checkequalityfmu :: "FMI2COMP" where
  fmus_distinct : "distinct [pdsgfmu1, pdsgfmu2, samplerfmu, checkequalityfmu]" and
  FMI2COMP_def : "FMI2COMP = {pdsgfmu1, pdsgfmu2, samplerfmu, checkequalityfmu}"

subsection {* Parameters *}

text {* I am not sure about the below. Perhaps ask Ana and/or Jim. *}

overloading
  D2_2d_parameters \<equiv> "parameters :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
  definition D2_2d_parameters :: "(FMI2COMP \<times> VAR \<times> VAL) list" where
  "D2_2d_parameters = [
    (pdsgfmu1, $x:{nat}\<^sub>u, InjU (1::nat)),
    (pdsgfmu1, $y:{nat}\<^sub>u, InjU (1::nat)),
    (pdsgfmu2, $x:{nat}\<^sub>u, InjU (1::nat)),
    (pdsgfmu2, $y:{nat}\<^sub>u, InjU (1::nat))]"
end

subsection {* Inputs *}

overloading
  D2_2d_inputs \<equiv> "inputs :: (FMI2COMP \<times> VAR) list"
begin
  definition D2_2d_inputs :: "(FMI2COMP \<times> VAR) list" where
  "D2_2d_inputs = [
    (samplerfmu, $x:{nat}\<^sub>u),
    (samplerfmu, $y:{nat}\<^sub>u),
    (checkequalityfmu, $y:{nat}\<^sub>u),
    (checkequalityfmu, $z:{nat}\<^sub>u)]"
end

overloading
  D2_2d_initialValues \<equiv> "initialValues :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
  definition D2_2d_initialValues :: "(FMI2COMP \<times> VAR \<times> VAL) list" where
  "D2_2d_initialValues = [
    (samplerfmu, $x:{nat}\<^sub>u, InjU (1::nat)),
    (samplerfmu, $y:{nat}\<^sub>u, InjU (1::nat)),
    (checkequalityfmu, $y:{nat}\<^sub>u, InjU (1::nat)),
    (checkequalityfmu, $z:{nat}\<^sub>u, InjU (1::nat))]"
end

subsection {* Outputs *}

overloading
  D2_2d_outputs \<equiv> "outputs :: (FMI2COMP \<times> VAR) list"
begin
  definition D2_2d_outputs :: "(FMI2COMP \<times> VAR) list" where
  "D2_2d_outputs = [
    (pdsgfmu1, $x:{nat}\<^sub>u),
    (pdsgfmu2, $y:{nat}\<^sub>u),
    (samplerfmu, $z:{nat}\<^sub>u)]"
end

subsection {* Simulation Parameters *}

overloading D2_2d_startTime \<equiv> "startTime :: TIME('\<tau>)"
begin
  definition D2_2d_startTime :: "TIME('\<tau>)" where
  "D2_2d_startTime = 0"
end

overloading D2_2d_stopTimeDefined \<equiv> "stopTimeDefined :: bool"
begin
  definition D2_2d_stopTimeDefined :: "bool" where
  "D2_2d_stopTimeDefined = True"
end

overloading D2_2d_stopTime \<equiv> "stopTime :: TIME('\<tau>)"
begin
  definition D2_2d_stopTime :: "TIME('\<tau>)" where
  "D2_2d_stopTime = 5"
end
end