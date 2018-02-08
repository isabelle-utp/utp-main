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
    "UTP-Toolkit"
  theories
    Derivative_extra
    Contiguous_Functions
    Timed_Traces
  document_files
    "root.bib"
    "root.tex"
    "document.sty"
    "zed.sty"
    "csp.sty"

(* UTP Mathematical Toolkit *)

session "UTP-Toolkit" in "toolkit" = "HOL-Algebra" +
  options [document = pdf, document_output = "output", timeout = 1000]
  sessions
    Optics
  theories utp_toolkit
  document_files
    "root.tex"
    "root.bib"
    "document.sty"

(* Core UTP Framework *)

session "UTP" in "utp" = "UTP-Toolkit" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* UTP Designs *)

session "UTP-Designs" in "theories/designs" = "UTP" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp_designs
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Imperative Programs based on Designs *)
    
session "UTP-Impl" in "impl" = "UTP-Designs" +
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

(* Core UTP with Deep Variables *)

session "UTP-Deep" in "utp/models" = "UTP" +
  options [browser_info = true, document = false]
  sessions
    Continuum
  theories utp_deep

(* Core UTP with Axiomatic Variables *)

session "UTP-Axm" in "utp/models" = "UTP" +
  options [browser_info = true, document = false]
  theories utp_axm

(* Core UTP with Deep & Axiomatic Variables *)

session "UTP-Deep-Axm" in "utp/models" = "UTP-Deep" +
  options [browser_info = true, document = false]
  theories utp_deep utp_axm

(* UTP Theory Base *)

session "UTP-Theories" in "theories" = "UTP-Reactive" +
  options [browser_info = true, document = false]
  theories utp_theories

session "UTP-Theories-Deep" in "theories" = "UTP-Theories" +
  options [browser_info = true, document = false]
  sessions
    "UTP-Deep"
  theories utp_theories_deep

session "UTP-Theories-Axm" in "utp/models" = "UTP-Theories" +
  options [browser_info = true, document = false]
  sessions
    "UTP-Axm"
  theories utp_theories utp_axm

session "UTP-Theories-Deep-Axm" in "utp/models" = "UTP-Theories-Deep" +
  options [browser_info = true, document = false]
  sessions
    "UTP-Deep-Axm"
  theories utp_theories_deep utp_axm

(* Imports for Hybrid UTP *)

(* We chose to start another root from the Analysis session (via Dynamics)
   and build everything else on top of it. This is because Analysis takes
   more than 10 minutes to build on a laptop and everything else is
   comparatively lightweight. *)

session "UTP-Hybrid-Imports" = "Dynamics" +
  options [document = false]
  sessions
    "UTP-Theories"
  theories
    "hybrid/utp_hybrid_imports"

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