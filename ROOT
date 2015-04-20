session "HOL-UTP-IMPORTS" = "Kleene_Algebra" +
  options [browser_info = true, document = false]
    theories "theories/utp_imports"
  files "document/root.tex"

session "HOL-UTP" = "HOL-UTP-IMPORTS" +
  options [browser_info = true, document = pdf, document_output = "output", document_graph = true, document_variants="document:outline=/proof,/ML"]
  theories [document = false]
  theories
    "theories/utp_base"
    "theories/utp_friendly"
 (* "theories/models/utp_basic_model" *)
  files "document/root.tex"

session "HOL-UTP-DES" in "theories/theories/designs" = "HOL-UTP" +
  options [document = pdf, document_output = "output"]
  theories
    "utp_designs"
  files "document/root.tex"

session "HOL-UTP-REA" in "theories/theories/reactive" = "HOL-UTP-DES" +
  options [document = pdf, document_output = "output"]
  theories
    "utp_reactive"
  files "document/root.tex"

session "HOL-UTP-THY" in "theories/theories" = "HOL-UTP-REA" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories
    "utp_acp"
    "utp_csp"
    "utp_definedness"
  files "document/root.tex"

session "HOL-UTP-CML" in "theories/models/utp_cml_new" = "HOL-UTP-THY" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories
    "utp_cml"
  files "document/root.tex"

session "HOL-UTP-CML-SIMP" in "theories/models/utp_cml_simp" = "HOL-UTP-THY" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories
    "utp_cml_model"
  files "document/root.tex"
  
session "HOL-UTP-CML-EX" in "theories/models/utp_cml/examples" = "HOL-UTP-CML" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories
    "utp_cml_examples"
  files "document/root.tex"

session "utp-hjf-summer-school" in "papers/utp-hjf-summer-school" = "HOL-UTP-THY" +
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

session "utp-mrktdrf-2014" in "papers/utp-mrktdrf-2014" = "HOL-UTP-THY" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
  theories
    "theory_mechanisation"
    "hoare_gcd"
    "isabelle_utp"
    "proof_basic_laws"
    "proof_design_comp"
    "proof_des_design"
    "proof_des_inj"
    "proof_h1_algebraic"
    "proof_h1_equiv"
    "proof_h1_h2_design"
    "proof_h1_left_unit"
    "proof_h1_left_zero"
    "proof_h2_equiv"
    "proof_h2_idempotent"
    "proof_h3"
    "proof_h4_form"
    "proof_iter_unfold"
    "proof_j_is_h2"
    "proof_j_split"
    "proof_refinement_conditional"
    "proof_rel_design"
    "proof_rel_des"
    "proof_unreachable_branch"
    "proof_unreachable_branch_single"
    "proof_wp"
  files
    "document/root.tex"
    "document/mdrf.bib"

session "isabelle-basics-tutorial" in "papers/isabelle-basics-tutorial" = "HOL" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories
    "BasicProofs"
    "Dates"
    "Deduction"
    "Trees"

session "isabelle-utp-tutorial" in "papers/isabelle-utp-tutorial" = "HOL-UTP-THY" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories [document = false]
  theories
    "value_class"
    "bindings"
    "cantor_isar"
    "predicates"
    "unrest"
    "designs_basics"
    "designs_healths"
    "proof_missing_unreachable_branch"
    "proof_unreachable_branch"
    "proof_refinement_conditional"
    "proof_h1_left_zero"
    "proof_h1_left_unit"
    "utp_pred_tac_proofs"
    "utp_rel_tac_proofs"
    "utp_types"
  files "document/root.tex"

session "designs-tutorial" in "papers/designs-tutorial" = "HOL-UTP" +
  options [document = pdf, document_output = "output"]
  theories
    "utp_designs"
  files "document/root.tex"

session "avocs2013" in "papers/avocs2013" = "HOL-UTP" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
  theories
    "proof_unreachable_branch"
    "proof_refinement_conditional"
  files "document/root.tex"

session "nfm2014" in "papers/nfm2014" = "HOL-UTP" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories [document = false]
  theories
    "prelim"
    "deep_shallow"
    "prog_model"
    "poly_expr"
    "tactics"
    "shallow_values"
  files
    "document/root.tex"
    "document/nfm2014.bib"
    "document/deep-shallow.pdf"

session "utp2014" in "papers/utp2014" = "HOL-UTP-THY" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories [document = false]
  theories 
    "prelim"
    "h1_h2_design"
    "prog_model"
    "poly_expr"
    "tactics"
  files "document/root.tex"
        "document/utp2014.bib"
        "document/deep-shallow.pdf"

session "utp2014-presentation" in "papers/utp2014-presentation" = "HOL-UTP" +
  options [document = pdf, document_output = "output", quick_and_dirty = true]
  theories
    "value_class"
    "bindings"
    "pred_ops"
    "alpha_unrest"
    "expr"
    "sort_class"
    "poly_expr"
    "poly_erasure"
  files "document/root.tex"

session Datatype_Order_Generator (AFP) in "contrib/Datatype_Order_Generator"
  = "HOL-Library" +
  options [timeout = 600]
  theories [document=false]
    "../Collections/Lib/HashCode"
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
    Kleene_Algebras
    Kleene_Algebra_Models
    Matrix
    Omega_Algebra
    Omega_Algebra_Models
    Signatures
  files
    "document/root.bib"
    "document/root.tex"
