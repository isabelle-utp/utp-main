session "HOL-UTP" = "Kleene_Algebra" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
  theories 
  "theories/utp_base"
  "theories/utp_meta"
  files "document/root.tex"

session "HOL-UTP-VDM" in "theories/models/utp_vdm_simple" = "HOL-UTP" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories [document = false]
  "utp_vdm_values"
  "utp_vdm_inject"
  "utp_vdm_sorts"
  "utp_vdm_expr"
  "utp_vdm_types"
  "utp_vdm_functions"
  "utp_vdm"

session "utp-hjf-summer-school" in "papers/utp-hjf-summer-school" = "HOL-UTP" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
  theories 
    "theory_mechanisation"
    "proof_basic_laws"
    "proof_design_comp"
    "proof_h1_algebraic"
    "proof_h1_equiv"
    "proof_h1_h2_design"
    "proof_h1_left_unit"
    "proof_h1_left_zero"
    "proof_h2_equiv"
    "proof_h2_idempotent"
    "proof_j_is_h2"
    "proof_j_split"
    "proof_refinement_conditional"
    "proof_unreachable_branch"
    "proof_wp"
  files "document/root.tex"

session "isabelle-basics-tutorial" in "papers/isabelle-basics-tutorial" = "HOL" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories
    "BasicProofs"
    "Dates"
    "Deduction"
    "Trees"

session "isabelle-utp-tutorial" in "papers/isabelle-utp-tutorial" = "HOL-UTP-VDM" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories [document = false]
  theories 
    "vdm_expressions"
    "value_class"
    "bindings"
    "predicates"
    "unrest"
    "designs_basics"
    "designs_healths"
    "proof_missing_unreachable_branch"
    "proof_unreachable_branch"
    "proof_refinement_conditional"
    "proof_h1_left_zero"
    "proof_h1_left_unit"
  files "document/root.tex"

session "avocs2013" in "papers/avocs2013" = "HOL-UTP" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
  theories 
    "proof_unreachable_branch"
    "proof_refinement_conditional"
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
