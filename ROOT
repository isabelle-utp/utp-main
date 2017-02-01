(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: ROOT                                                                 *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

(* Third-party Contributions *)

session Kleene_Algebra (AFP) in "contrib/Kleene_Algebra"
  = "HOL-Multivariate_Analysis" +
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

session "UTP-IMPORTS" in "utils" = "UTP-DEPS" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    cardinals
    Continuum
    finite_bijection
    Dyadic
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
    "Library_extra/Derivative_extra"
    Positive
    Real_Bit
    ttrace
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
