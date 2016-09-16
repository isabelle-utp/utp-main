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

session "UTP-IMPORTS" in "utils" = "Kleene_Algebra" +
  options [timeout = 600]
  theories
    cardinals
    Continuum
    finite_bijection
    Dyadic
    Lenses
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

session "UTP" in "utp" = "UTP-IMPORTS" +
  options [document = pdf, document_output = "output", timeout = 1000]
  theories
    utp
  document_files 
    "root.tex"
    "document.sty"

session "VDM-SL" in "vdm-sl" = "UTP" +
  options [document = none]
  theories
    PFOL
    VDM
