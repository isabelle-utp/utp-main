header {* \isaheader{Entry Point with genCF and original ICF} *}
theory Refine_Dflt_ICF
imports 
  "../Refine_Monadic/Refine_Monadic"
  "GenCF/GenCF"
  "ICF/Collections"
  "Lib/Code_Target_ICF"
begin


text {* Contains the Monadic Refinement Framework, the generic collection 
  framework and the original Isabelle Collection Framework *}

declaration {* let open Autoref_Fix_Rel in fn phi =>
  I 
  #> declare_prio "Gen-RBT-set" @{cpat "\<langle>?R\<rangle>dflt_rs_rel"} PR_LAST phi
  #> declare_prio "RBT-set" @{cpat "\<langle>?R\<rangle>rs.rel"} PR_LAST phi
  #> declare_prio "Hash-set" @{cpat "\<langle>?R\<rangle>hs.rel"} PR_LAST phi
  #> declare_prio "List-set" @{cpat "\<langle>?R\<rangle>lsi.rel"} PR_LAST phi
end *}

declaration {* let open Autoref_Fix_Rel in fn phi =>
  I 
  #> declare_prio "RBT-map" @{cpat "\<langle>?Rk,?Rv\<rangle>rm.rel"} PR_LAST phi
  #> declare_prio "Hash-map" @{cpat "\<langle>?Rk,?Rv\<rangle>hm.rel"} PR_LAST phi
  (*#> declare_prio "Gen-RBT-map" @{cpat "\<langle>?Rk,?Rv\<rangle>rbt_map_rel ?cmp"} PR_LAST phi*)
  #> declare_prio "List-map" @{cpat "\<langle>?Rk,?Rv\<rangle>lmi.rel"} PR_LAST phi
end *}

text "Fallbacks"
declaration {*
  let open Autoref_Fix_Rel in fn phi =>
    I
    #> declare_prio "Gen-List-Set" @{cpat "\<langle>?R\<rangle>list_set_rel"} PR_LAST phi
    #>  declare_prio "Gen-List-Map" @{cpat "\<langle>?Rk,?Rv\<rangle>list_map_rel"} PR_LAST phi
  end
*}

class id_refine

instance nat :: id_refine ..
instance bool :: id_refine ..
instance int :: id_refine ..

lemmas [autoref_tyrel] = 
  ty_REL[where 'a="nat" and R="nat_rel"]
  ty_REL[where 'a="int" and R="int_rel"]
  ty_REL[where 'a="bool" and R="bool_rel"]
lemmas [autoref_tyrel] = 
  ty_REL[where 'a="nat set" and R="\<langle>Id\<rangle>rs.rel"]
  ty_REL[where 'a="int set" and R="\<langle>Id\<rangle>rs.rel"]
  ty_REL[where 'a="bool set" and R="\<langle>Id\<rangle>lsi.rel"]
lemmas [autoref_tyrel] = 
  ty_REL[where 'a="(nat \<rightharpoonup> 'b)", where R="\<langle>nat_rel,Rv\<rangle>dflt_rm_rel"]
  ty_REL[where 'a="(int \<rightharpoonup> 'b)", where R="\<langle>int_rel,Rv\<rangle>dflt_rm_rel"]
  ty_REL[where 'a="(bool \<rightharpoonup> 'b)", where R="\<langle>bool_rel,Rv\<rangle>dflt_rm_rel"]
  for Rv

lemmas [autoref_tyrel] = 
  ty_REL[where 'a="(nat \<rightharpoonup> 'b::id_refine)", where R="\<langle>nat_rel,Id\<rangle>rm.rel"]
  ty_REL[where 'a="(int \<rightharpoonup> 'b::id_refine)", where R="\<langle>int_rel,Id\<rangle>rm.rel"]
  ty_REL[where 'a="(bool \<rightharpoonup> 'b::id_refine)", where R="\<langle>bool_rel,Id\<rangle>rm.rel"]

end
