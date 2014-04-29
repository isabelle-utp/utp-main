header {* \isaheader{Generic Collection Framework (Internal)} *}
theory GenCF
imports 
  "Impl/Impl_List_Set" 
  "Impl/Impl_List_Map" 
  "Impl/Impl_RBT_Map" 
  "Impl/Impl_Array_Map"
  "Impl/Impl_Array_Hash_Map"
  "Impl/Impl_Array_Stack"
  "Impl/Impl_Cfun_Set"
  "Gen/Gen_Set"
  "Gen/Gen_Map"
  "Gen/Gen_Map2Set"
  "Gen/Gen_Comp"
  "~~/src/HOL/Library/Code_Target_Numeral"

begin

  text {* Use one of the @{text "Refine_Dflt"}-theories as entry-point! *}

  text {* Useful Abbreviations *}
  abbreviation "dflt_rs_rel \<equiv> map2set_rel dflt_rm_rel"
  abbreviation "iam_set_rel \<equiv> map2set_rel iam_map_rel"
  abbreviation "dflt_ahs_rel \<equiv> map2set_rel dflt_ahm_rel"

end
