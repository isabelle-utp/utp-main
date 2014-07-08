header {* \isaheader{Default Setup} *}
theory Refine_Dflt
imports 
  "../Refine_Monadic/Refine_Monadic"
  "GenCF/GenCF"
  "~~/src/HOL/Library/Code_Target_Numeral"
begin

text {* Configurations *}

lemmas tyrel_dflt_nat_set[autoref_tyrel] = 
  ty_REL[where 'a="nat set" and R="\<langle>Id\<rangle>dflt_rs_rel"]

lemmas tyrel_dflt_bool_set[autoref_tyrel] = 
  ty_REL[where 'a="bool set" and R="\<langle>Id\<rangle>list_set_rel"]

lemmas tyrel_dflt_nat_map[autoref_tyrel] = 
  ty_REL[where R="\<langle>nat_rel,Rv\<rangle>dflt_rm_rel", standard]

lemmas tyrel_dflt = tyrel_dflt_nat_set tyrel_dflt_bool_set tyrel_dflt_nat_map


declaration {* let open Autoref_Fix_Rel in fn phi =>
  I 
  #> declare_prio "Gen-AHM-map-hashable" 
    @{cpat "\<langle>?Rk::(_\<times>_::hashable) set,?Rv\<rangle>ahm_rel ?bhc"} PR_LAST phi
  #> declare_prio "Gen-RBT-map-linorder" 
    @{cpat "\<langle>?Rk::(_\<times>_::linorder) set,?Rv\<rangle>rbt_map_rel ?lt"} PR_LAST phi
  #> declare_prio "Gen-AHM-map" @{cpat "\<langle>?Rk,?Rv\<rangle>ahm_rel ?bhc"} PR_LAST phi
  #> declare_prio "Gen-RBT-map" @{cpat "\<langle>?Rk,?Rv\<rangle>rbt_map_rel ?lt"} PR_LAST phi
end *}


text "Fallbacks"
declaration {*
  let open Autoref_Fix_Rel in fn phi =>
    I
    #> declare_prio "Gen-List-Set" @{cpat "\<langle>?R\<rangle>list_set_rel"} PR_LAST phi
    #>  declare_prio "Gen-List-Map" @{cpat "\<langle>?R\<rangle>list_map_rel"} PR_LAST phi
  end
*}

end
