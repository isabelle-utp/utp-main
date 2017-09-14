(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: ROOT                                                                 *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

(* AFP Contributions *)

session "HOL-Algebra2" (main timing) in "contrib/Algebra" = HOL +
  description {*
    Author: Clemens Ballarin, started 24 September 1999

    The Isabelle Algebraic Library.
  *}
  theories [document = false]
    (* Preliminaries from set and number theory *)
    "~~/src/HOL/Library/FuncSet"
    "~~/src/HOL/Number_Theory/Primes"
    "~~/src/HOL/Library/Permutation"
  theories [document = pdf]
    (*** New development, based on explicit structures ***)
    (* Groups *)
    FiniteProduct        (* Product operator for commutative groups *)
    Sylow                (* Sylow's theorem *)
    Bij                  (* Automorphism Groups *)

    (* Orders and Lattices *)
    Order
    Lattice
    Complete_Lattice
    Galois_Connection

    (* Rings *)
    Divisibility         (* Rings *)
    IntRing              (* Ideals and residue classes *)
    UnivPoly             (* Polynomials *)
  document_files
    "root.bib"
    "root.tex"

(* Optics Library *)

session "Optics" in "optics"
  = (* "HOL-Algebra2" *) "HOL" +
  options [document = pdf, document_output = "output", timeout = 300]
  theories
    Interp
    Two
    Lens_Laws
    Lens_Algebra
    Lens_Order
    Lens_Instances
    Lenses
  document_files
    "root.bib"
    "root.tex"
    "document.sty"
    "figures/Lens.pdf"
    "figures/Independence.pdf"
    "figures/Sum.pdf"
    "figures/Composition.pdf"

(* Continuum Universe *)

session "Continuum" in "continuum" = "HOL-Cardinals" +
  options [document = false, timeout = 1000]
  theories
    Continuum
    Dyadic
    Finite_Bijection
    (* Infinity *)
    Lightweight_Cardinals
    Real_Bit
    UNIV_TYPE

(* Continuous System Dynamics *)

session "Dynamics" in "dynamics" = "HOL-Analysis" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    "../contrib/Ordinary_Differential_Equations/ODE_Analysis"
    Derivative_extra
    Contiguous_Functions
    Timed_Traces
  document_files
    "root.bib"
    "root.tex"
    "document.sty"
    "zed.sty"
    "csp.sty"

(* Library Imports for UTP *)

session "UTP-IMPORTS" in "utils" = "HOL-Algebra2" +
  options [document = false, timeout = 1000]
  theories utp_imports

(* Core UTP Framework *)

session "UTP" in "utp" = "UTP-IMPORTS" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories utp
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Core UTP with Deep Variables *)

session "UTP-DEEP" in "utp/models" = "UTP" +
  options [browser_info = true, document = false]
  theories utp_deep

(* Core UTP with Axiomatic Variables *)

session "UTP-AXM" in "utp/models" = "UTP" +
  options [browser_info = true, document = false]
  theories utp_axm

(* Core UTP with Deep & Axiomatic Variables *)

session "UTP-DEEP-AXM" in "utp/models" = "UTP-DEEP" +
  options [browser_info = true, document = false]
  theories utp_deep utp_axm

(* UTP Theory Base *)

session "UTP-THY" in "theories" = "UTP" +
  options [browser_info = true, document = false]
  theories utp_theories

session "UTP-THY-DEEP" in "theories" = "UTP-THY" +
  options [browser_info = true, document = false]
  theories utp_theories_deep

session "UTP-THY-AXM" in "utp/models" = "UTP-THY" +
  options [browser_info = true, document = false]
  theories utp_theories utp_axm

session "UTP-THY-DEEP-AXM" in "utp/models" = "UTP-THY-DEEP" +
  options [browser_info = true, document = false]
  theories utp_theories_deep utp_axm

(* Imports for Hybrid UTP *)

(* We chose to start another root from the Analysis session (via Dynamics)
   and build everything else on top of it. This is because Analysis takes
   more than 10 minutes to build on a laptop and everything else is
   comparatively lightweight. *)

session "UTP-HYBRID-IMPORTS" = "Dynamics" +
  options [document = false]
  theories
    "~~/src/HOL/Library/FuncSet"
    "~~/src/HOL/Library/Permutation"
    "contrib/Algebra/Complete_Lattice"
    "contrib/Algebra/Galois_Connection"
    "utils/utp_imports"
    "utp/utp"
    "theories/utp_theories"

(* Hybrid UTP *)

session "UTP-HYBRID" in "hybrid" = "UTP-HYBRID-IMPORTS" +
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

session "UTP-HYBRID-DEEP" in "theories" = "UTP-HYBRID" +
  options [browser_info = true, document = false]
  theories utp_theories_deep

(* Hybrid UTP examples *)

session "UTP-HYBRID-EXAMPLES" in "hybrid/examples" = "UTP-HYBRID" +
  options [document = false]
  theories
    utp_bouncing_ball
    utp_thermostat
    utp_trains

(* Modelica Mechanisation *)

session "Modelica" in "modelica" = "UTP-HYBRID" +
  options [document = false]
  theories
    Modelica

(* VDM-SL Mechanisation *)

session "VDM-SL" in "vdm-sl" = "UTP-THY-DEEP" +
  options [document = false]
  theories
    PFOL
    VDM

(* Isabelle/UTP Tutorial *)

session "UTP-TUTORIAL" in "tutorial" = "UTP-THY" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    utp_tutorial
    utp_boyle
    utp
    utp_csp_buffer
    utp_csp_mini_mondex
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* FMI Mechanisation *)

session "FMI" in "fmi" = "UTP-THY-DEEP-AXM" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    fmi
    Time
    Railways
    Topology
    Interlocking
  document_files
    (* "root.bib" *)
    "root.tex"
    "document.sty"
