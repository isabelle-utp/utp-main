(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: ROOT                                                                 *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@gmail.com                  *)
(******************************************************************************)

(* Profiling Library *)

session "Profiling" in "profiling" = "HOL-Eisbach" +
  options [document = false, timeout = 1000]
  theories
    Profiling

(* Continuum Universe *)

session "Continuum" in "continuum" = "HOL-Cardinals" +
  options [document = false, timeout = 1000]
  sessions
    "UTP1-Toolkit"
  theories
    Continuum
    Dyadic
    Finite_Bijection
    Lightweight_Cardinals
    Real_Bit
    UNIV_TYPE

(* Continuous System Dynamics *)

session "Dynamics" in "dynamics" = "Ordinary_Differential_Equations" +
  options [document = pdf, document_output = "output", timeout = 1000]
  sessions
    "UTP1-Reactive"
    "Differential_Dynamic_Logic"
  theories
    Derivative_extra
    ODE_Cert
    Contiguous_Functions
    Timed_Traces
    Matrix_Syntax
  document_files
    "root.bib"
    "root.tex"
    "document.sty"
    "zed.sty"
    "csp.sty"

(* UTP Mathematical Toolkit *)

session "UTP1-Toolkit" in "toolkit" = "HOL-Algebra" +
  options [document = false]
  sessions
    Optics
    Z_Toolkit
    Total_Recall
  theories utp_toolkit

(* Core UTP Framework *)

session "UTP1" in "utp" = "UTP1-Toolkit" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories [document = false]
    utp_parser_utils
  theories
    utp
    utp_full
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* UTP Calculi *)

session "UTP1-Calculi" in "calculi" = "UTP1" +
  options [document = false]
  theories
    utp_wprespec

(* Pseudo Z-Notation *)

session "ZedLite" in "zedlite" = "UTP1" +
  options [document = false]
  theories [document = false]
    zedlite

(* UTP and Kleene Algebra with Tests (KAT) *)

session "UTP1-KAT" in "theories/kleene" = "UTP1" +
  options [document = pdf, document_output = "output", timeout = 1000]
  sessions
    "KAT_and_DRA"
  theories utp_kleene
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* UTP Designs *)

session "UTP1-Designs" in "theories/designs" = "UTP1-KAT" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_designs
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* UTP Undefinedness *)

session "UTP1-Undef" in "theories/undef" = "UTP1-Designs" +
  options [document = false]
  theories utp_undef

(* UTP Memory Models *)

session "UTP1-Memory" in "theories/memory" = "UTP1-Undef" +
  options [document = false]
  sessions
    "Continuum"
  theories utp_memory

(* Imperative Programs based on Designs *)

session "UTP1-Impl" in "impl" = "UTP1-Memory" +
  options [document = false]
  theories
    utp_impl

(* UTP Generalised Reactive Processes *)

session "UTP1-Reactive" in "theories/reactive" = "UTP1-Designs" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_reactive
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Reactive Designs *)

session "UTP1-Reactive-Designs" in "theories/rea_designs" = "UTP1-Reactive" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_rea_designs
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Timed Relations *)

session "UTP1-Time" in "theories/time" = "UTP1-Reactive-Designs" +
  options [browser_info = true, document = false]
  theories utp_time_rel

(* Stateful-Failure Reactive Designs *)

session "UTP1-Stateful-Failures" in "theories/sf_rdes" = "UTP1-Reactive-Designs" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_sf_rdes
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Circus *)

session "UTP1-Circus" in "theories/circus" = "UTP1-Stateful-Failures" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_circus utp_circus_easy_parser
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Core UTP with Deep Variables *)

session "UTP1-Deep" in "utp/models/deep" = "UTP1" +
  options [browser_info = true, document = false]
  sessions Continuum
  theories utp_deep

(* Core UTP with Axiomatic Variables *)

session "UTP1-Axm" in "utp/models/axm" = "UTP1" +
  options [browser_info = true, document = false]
  directories "../../../axiomatic"
  theories utp_axm

(* Core UTP with Deep & Axiomatic Variables *)

session "UTP1-Deep-Axm" in "utp/models" = "UTP1-Deep" +
  options [browser_info = true, document = false]
  sessions "UTP1-Axm"
  theories "UTP1-Deep.utp_deep" "UTP1-Axm.utp_axm"

(* UTP Theory Base *)

session "UTP1-Theories" in "theories" = "UTP1-Circus" +
  options [browser_info = true, document = false]
  sessions
    "UTP1-Time"
  theories utp_theories

(* Imports for Hybrid UTP *)

(* We chose to start another root from the Analysis session (via Dynamics)
   and build everything else on top of it. This is because Analysis takes
   more than 10 minutes to build on a laptop and everything else is
   comparatively lightweight. *)

session "UTP1-Hybrid-Imports" in "hybrid/imports" = "Dynamics" +
  options [document = false]
  sessions
    "UTP1-Time"
  theories
    "utp_hybrid_imports"

(* Hybrid UTP *)

session "UTP1-Hybrid" in "hybrid" = "UTP1-Hybrid-Imports" +
  options [document = false, timeout = 1000]
  theories
    utp_hybrid
  document_files
    "root.bib"
    "root.tex"
    "document.sty"
    "zed.sty"
    "csp.sty"

(*
session "UTP1-dL" in "theories/hyprog" = "UTP1-Hybrid-Imports" +
  options [document = false]
  theories
    utp_hyprog

(* Hybrid UTP with deep model *)

session "UTP1-Hybrid-Deep" in "theories" = "UTP1-HYBRID" +
  options [browser_info = true, document = false]
  theories utp_theories_deep
*)

(* Hybrid UTP examples *)

session "UTP1-Hybrid-Examples" in "hybrid/examples" = "UTP1-Hybrid" +
  options [document = false]
  theories
    utp_bouncing_ball
    utp_thermostat
    utp_trains

(* Modelica Mechanisation: Limited Compositional Semantics *)

session "Modelica" in "modelica" = "UTP1-Hybrid" +
  options [document = false]
  theories
    Modelica

(* Modelica Mechanisation: Non-Compositional Semantics *)

session "Modelica-NC" in "modelica/noncomp" = "UTP1-Hybrid" +
  options [document = false]
  theories
    Modelica_NonComp

(*
(* VDM-SL Mechanisation *)

session "VDM-SL" in "vdm-sl" = "UTP1-THY-DEEP" +
  options [document = false]
  theories
    PFOL
    VDM
*)

(* Isabelle/UTP Tutorial *)

session "UTP1-Tutorial" in "tutorial" = "UTP1-Theories" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    utp_tutorial
    utp_boyle
    utp_csp_buffer
    utp_csp_mini_mondex
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Untimed RoboChart *)

(*
session "RoboChart-Untimed" in "robochart/untimed" = "UTP1-Circus" +
  theories
    MetaModel
    StateMachine
*)

(* FMI Mechanisation *)

(*
session "FMI" in "fmi" = "UTP1-Theories-Deep-Axm" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    fmi
    Time
    Topology
    Architecture
    Railways_Spec
    Railways_Impl
    Interlocking
  document_files
    (* "root.bib" *)
    "root.tex"
    "document.sty"
*)

(* Case Studies *)

session "Tokeneer" in "casestudies/Tokeneer" = "ZedLite" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    Tokeneer
  document_files
    "root.tex"
