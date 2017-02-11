(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: ROOT                                                                 *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

(* Third-party Contributions *)

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
  document_files "root.bib" "root.tex"

(* Kleene Algebra *)    

session Kleene_Algebra (AFP) in "contrib/Kleene_Algebra"
  = "HOL-Library" +
  options [timeout = 300]
  theories
    Action_Algebra
    Action_Algebra_Models
    Dioid
    Dioid_Models
    Kleene_Algebras
    Kleene_Algebra_Models
    Matrix
    Omega_Algebra
    Omega_Algebra_Models
    Quantales
    Signatures
  files
    "document/root.bib"
    "document/root.tex"

(* Lenses *)
    
session "Optics" in "lenses" 
  = "HOL-Algebra2" +
  options [timeout = 300]
  theories
    Interp
    Two
    Lens_Laws
    Lens_Algebra
    Lens_Order
    Lens_Instances
    Lenses

(* Continuum Universe *)
    
session "Continuum" in "continuum" = "HOL-Cardinals" +
  options [document = false, timeout = 1000]
  theories
    Continuum
    Dyadic
    Finite_Bijection
    Infinity
    Lightweight_Cardinals
    Real_Bit
    UNIV_TYPE

(* Continuous system dynamics *)
    
session "Dynamics" in "dynamics" = "HOL-Analysis" +
  options [document = false, timeout = 1000]
  theories
    Derivative_extra
    Contiguous_Functions
    Timed_Traces
    
(* UTP library imports *)

session "UTP-IMPORTS" in "utils" = "Optics" +
  options [document = false, timeout = 1000]
  theories
    "~~/src/HOL/Eisbach/Eisbach"
    "~~/src/Tools/Adhoc_Overloading"
    "~~/src/HOL/Library/Char_ord"
    "~~/src/HOL/Library/Countable_Set"
    "~~/src/HOL/Library/FSet"
    "~~/src/HOL/Library/Monad_Syntax"
    "~~/src/HOL/Library/Prefix_Order"
    "~~/src/HOL/Library/Sublist"
    Profiling
    "Library_extra/FSet_extra"
    "Library_extra/List_extra"
    "Library_extra/List_lexord_alt"
    "Library_extra/Monoid_extra"
    "Library_extra/Pfun"
    "Library_extra/Ffun"

(* Imports including the axiomatic value model *)

session "UTP-IMPORTS-AX" in "axiomatic/theories" = "UTP-IMPORTS" +
  options [browser_info = true, document = false]
  theories "core/ulens" "core/udefaults"

(* Core UTP framework *)

session "UTP" in "utp" = "UTP-IMPORTS" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    utp
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Imports including deep variables *)
    
session "UTP-DEEP" in "deep" = "UTP" +
  options [browser_info = true, document = false]
  theories
    "../continuum/Continuum"
    utp_deep
    
(* Core framework including the axiomatic value model *)

session "UTP-AX" in "utp" = "UTP-IMPORTS-AX" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    utp_ax
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* Imports for Hybrid UTP *)

(* We chose to start another root from the Analysis session (via Dynamics) 
   and build everything else on top of it. This is because Analysis takes 
   more than 10 minutes to build on a laptop and everything else is 
   comparatively lightweight. *)

session "UTP-HY-IMPORTS" = "Dynamics" +
  options [document = false]
  theories
    "~~/src/HOL/Library/FuncSet"
    "~~/src/HOL/Library/Permutation"
    "contrib/Algebra/Complete_Lattice"
    "contrib/Algebra/Galois_Connection"
    "contrib/Ordinary_Differential_Equations/ODE_Analysis"
    "utp/utp"

(* Hybrid UTP *)

session "UTP-Hybrid" in "hybrid" = "UTP-HY-IMPORTS" +
  options [document = false]
  theories
    utp_hybrid

(* VDM-SL Mechanisation *)

session "VDM-SL" in "vdm-sl" = "UTP-DEEP" +
  options [document = false]
  theories
    PFOL
    VDM
