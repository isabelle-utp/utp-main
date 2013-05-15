session "HOL-UTP" = "Kleene_Algebra" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
  theories 
  "theories/utp_base"
  "theories/utp_meta"
  files "document/root.tex"

session "utp-hjf-summer-school" in "papers/utp-hjf-summer-school" = "HOL-UTP" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
  theories 
    "theory_mechanisation"
    "proof_unreachable_branch"
    "proof_refinement_conditional"
  files "document/root.tex"

session "isabelle-utp-tutorial" in "papers/isabelle-utp-tutorial" = "HOL-UTP" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories [document = false]
  theories 
    "value_class"
    "bindings"
    "predicates"
    "unrest"
    "designs_basics"
    "designs_healths"
    "proof_unreachable_branch"
    "proof_refinement_conditional"
    "proof_h1_left_zero"
    "proof_h1_left_unit"
  files "document/root.tex"

session Datatype_Order_Generator (AFP) in "contrib/Datatype_Order_Generator" 
  = "HOL-Library" +
  options [timeout = 300]
  theories [document=false]
    "../HashCode"
  theories
    Derive
    Derive_Examples
  files
    "document/root.bib"
    "document/root.tex"

session Kleene_Algebra (AFP) in "contrib/Kleene_Algebra"
  = "Datatype_Order_Generator" +
  options [timeout = 300]
  theories
    Action_Algebra
    Action_Algebra_Models
    Dioid
    Dioid_Models
    Kleene_Algebra
    Kleene_Algebra_Models
    Matrix
    Omega_Algebra
    Signatures
  files
    "document/root.bib"
    "document/root.tex"
