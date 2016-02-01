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

session "UTP" in "utp" = "Kleene_Algebra" +
  options [document = pdf, document_output = "output"]
  theories
    utp_var
    utp_dvar
    utp_expr
    utp_unrest
    utp_subst
    utp_lift
    utp_pred
    utp_rel
    utp_wp
    utp_procedure
    utp_theory
    utp_boyle
    utp_designs
    utp_concurrency
    utp_reactive
  document_files 
    "root.tex"
    "document.sty"

session "VDM-SL" in "vdm-sl" = "UTP" +
  options [document = none]
  theories
    PFOL
    VDM
