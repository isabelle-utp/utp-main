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

(* HOL library imports *)

session "UTP-DEPS" = "Kleene_Algebra" +
  options [timeout = 600]
  theories
    "~~/src/HOL/Cardinals/Cardinals"
    "~~/src/HOL/Eisbach/Eisbach"
    "~~/src/Tools/Adhoc_Overloading"
    "~~/src/HOL/Library/Char_ord"
    "~~/src/HOL/Library/Countable_Set_Type"
    "~~/src/HOL/Library/FSet"
    "~~/src/HOL/Library/Monad_Syntax"
    "~~/src/HOL/Library/Prefix_Order"
    "~~/src/HOL/Library/Sublist"
    "contrib/HOL-Algebra2/Complete_Lattice"
    "contrib/HOL-Algebra2/Galois_Connection"

(* UTP library imports *)

session "UTP-IMPORTS" in "utils" = "HOL" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    finite_bijection
    Lenses
    Profiling
    "Library_extra/Countable_Set_extra"
    "Library_extra/Fmap"
    "Library_extra/FSet_extra"
    "Library_extra/List_extra"
    "Library_extra/List_lexord_alt"
    "Library_extra/Monoid_extra"
    "Library_extra/Sequence"
    "Library_extra/Pfun"
    "Library_extra/Ffun"
    Positive
    interp
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

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

(* Core framework including the axiomatic value model *)

session "UTP-AX" in "utp" = "UTP-IMPORTS-AX" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    utp_ax
  document_files
    "root.bib"
    "root.tex"
    "document.sty"

(* VMD-SL Mechanisation *)

session "VDM-SL" in "vdm-sl" = "UTP" +
  options [document = none]
  theories
    PFOL
    VDM
