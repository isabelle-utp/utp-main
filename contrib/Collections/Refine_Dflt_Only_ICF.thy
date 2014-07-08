header {* \isaheader{Entry Point with only the ICF} *}
theory Refine_Dflt_Only_ICF
imports
  "../Refine_Monadic/Refine_Monadic"
  "ICF/Collections"
  "~~/src/HOL/Library/Code_Target_Numeral"
begin

text {* Contains the Monadic Refinement Framework and the original
  Isabelle Collection Framework. The generic collection framework is
  not included *}

declaration {* let open Autoref_Fix_Rel in fn phi =>
  I 
  #> declare_prio "RBT-set" @{cpat "\<langle>?R\<rangle>rs.rel"} PR_LAST phi
  #> declare_prio "Hash-set" @{cpat "\<langle>?R\<rangle>hs.rel"} PR_LAST phi
  #> declare_prio "List-set" @{cpat "\<langle>?R\<rangle>lsi.rel"} PR_LAST phi
end *}

declaration {* let open Autoref_Fix_Rel in fn phi =>
  I 
  #> declare_prio "RBT-map" @{cpat "\<langle>?Rk,?Rv\<rangle>rm.rel"} PR_LAST phi
  #> declare_prio "Hash-map" @{cpat "\<langle>?Rk,?Rv\<rangle>hm.rel"} PR_LAST phi
  #> declare_prio "List-map" @{cpat "\<langle>?Rk,?Rv\<rangle>lmi.rel"} PR_LAST phi
end *}


end
