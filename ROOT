(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: ROOT                                                                 *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

(* Profiling Library *)

session "Profiling" in "profiling"
  = "HOL" +
  options [document = false, timeout = 1000]
  theories
    Profiling

(* Continuum Universe *)

session "Continuum" in "continuum" = "HOL-Cardinals" +
  options [document = false, timeout = 1000]
  sessions
    "UTP-Toolkit"
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
    "UTP-Reactive"
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

session "UTP-Toolkit" in "toolkit" = "HOL-Algebra" +
  options [document = none]
  sessions
    Optics
    Z_Toolkit
    Total_Recall
  theories utp_toolkit

(* Core UTP Framework *)

session "UTP" in "utp" = "UTP-Toolkit" +
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

session "UTP-Calculi" in "calculi" = "UTP" +
  options [document = false]
  theories 
    utp_wprespec

(* Pseudo Z-Notation *)

session "ZedLite" in "zedlite" = "UTP" +
  options [document = false]
  theories [document = false]
    zedlite

(* UTP and Kleene Algebra with Tests (KAT) *)

session "UTP-KAT" in "theories/kleene" = "UTP" +
  options [document = pdf, document_output = "output", timeout = 1000]
  sessions
    "KAT_and_DRA"
  theories utp_kleene
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* UTP Designs *)

session "UTP-Designs" in "theories/designs" = "UTP-KAT" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_designs
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* UTP Undefinedness *)

session "UTP-Undef" in "theories/undef" = "UTP-Designs" +
  options [document = false]
  theories utp_undef

(* UTP Memory Models *)

session "UTP-Memory" in "theories/memory" = "UTP-Undef" +
  options [document = false]
  sessions
    "Continuum"
  theories utp_memory

(* Imperative Programs based on Designs *)
    
session "UTP-Impl" in "impl" = "UTP-Memory" +
  options [document = false]
  theories
    utp_impl

(* UTP Generalised Reactive Processes *)

session "UTP-Reactive" in "theories/reactive" = "UTP-Designs" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_reactive
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Reactive Designs *)

session "UTP-Reactive-Designs" in "theories/rea_designs" = "UTP-Reactive" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_rea_designs
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Timed Relations *)

session "UTP-Time" in "theories/time" = "UTP-Reactive-Designs" +
  options [browser_info = true, document = false]
  theories utp_time_rel  

(* Stateful-Failure Reactive Designs *)

session "UTP-Stateful-Failures" in "theories/sf_rdes" = "UTP-Reactive-Designs" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_sf_rdes
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Circus *)

session "UTP-Circus" in "theories/circus" = "UTP-Stateful-Failures" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_circus utp_circus_easy_parser
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Core UTP with Deep Variables *)

session "UTP-Deep" in "utp/models/deep" = "UTP" +
  options [browser_info = true, document = false]
  sessions
    Continuum
  theories utp_deep

(* Core UTP with Axiomatic Variables *)

session "UTP-Axm" in "utp/models/axm" = "UTP" +
  options [browser_info = true, document = false]
  theories utp_axm

(* Core UTP with Deep & Axiomatic Variables *)

session "UTP-Deep-Axm" in "utp/models" = "UTP-Deep" +
  options [browser_info = true, document = false]
  sessions "UTP-Axm"
  theories "UTP-Deep.utp_deep" "UTP-Axm.utp_axm"

(* UTP Theory Base *)

session "UTP-Theories" in "theories" = "UTP-Circus" +
  options [browser_info = true, document = false]
  sessions
    "UTP-Time"
  theories utp_theories

(* Imports for Hybrid UTP *)

(* We chose to start another root from the Analysis session (via Dynamics)
   and build everything else on top of it. This is because Analysis takes
   more than 10 minutes to build on a laptop and everything else is
   comparatively lightweight. *)

session "UTP-Hybrid-Imports" in "hybrid/imports" = "Dynamics" +
  options [document = false]
  sessions
    "UTP-Time"
  theories
    "utp_hybrid_imports"

(* Hybrid UTP *)

session "UTP-Hybrid" in "hybrid" = "UTP-Hybrid-Imports" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    utp_hybrid
  document_files
    "root.bib"
    "root.tex"
    "document.sty"
    "zed.sty"
    "csp.sty"

session "UTP-dL" in "theories/hyprog" = "UTP-Hybrid-Imports" +
  options [document = false]
  theories
    utp_hyprog

(* Hybrid UTP with deep model *)

(*
session "UTP-Hybrid-Deep" in "theories" = "UTP-HYBRID" +
  options [browser_info = true, document = false]
  theories utp_theories_deep
*)

(* Hybrid UTP examples *)

session "UTP-Hybrid-Examples" in "hybrid/examples" = "UTP-Hybrid" +
  options [document = false]
  theories
    utp_bouncing_ball
    utp_thermostat
    utp_trains
(*
(* Modelica Mechanisation: Limited Compositional Semantics *)

session "Modelica" in "modelica" = "UTP-HYBRID" +
  options [document = false]
  theories
    Modelica

(* Modelica Mechanisation: Non-Compositional Semantics *)

session "Modelica-NC" in "modelica/noncomp" = "UTP-HYBRID" +
  options [document = false]
  theories
    Modelica_NonComp
  
(* VDM-SL Mechanisation *)

session "VDM-SL" in "vdm-sl" = "UTP-THY-DEEP" +
  options [document = false]
  theories
    PFOL
    VDM
*)

(* Isabelle/UTP Tutorial *)

session "UTP-Tutorial" in "tutorial" = "UTP-Theories" +
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

session "RoboChart-Untimed" in "robochart/untimed" = "UTP-Circus" +
  theories
    MetaModel
    StateMachine

(* FMI Mechanisation *)

(*
session "FMI" in "fmi" = "UTP-Theories-Deep-Axm" +
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

