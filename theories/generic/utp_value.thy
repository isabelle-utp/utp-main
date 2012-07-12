(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_value.thy                                            *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Abstract Values *}

theory utp_value
imports "../utp_common" "../utp_sorts"
begin

subsection {* Locale @{term "VALUE"} *}

locale VALUE =
-- {* Typing Relation *}
  fixes type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
-- {* A type must not be empty. *}
  assumes type_non_empty : "\<exists> x . x : t"
  and     type_rel_total : "\<exists> t . x : t"
begin

subsection {* Universe *}

definition VALUE :: "'VALUE set" where
"VALUE = UNIV"

subsection {* Carrier Set *}

definition carrier :: "'TYPE \<Rightarrow> 'VALUE set" where
"carrier t = {x . x : t}"

theorem carrier_non_empty :
"\<forall> t . carrier t \<noteq> {}"
apply (auto simp: carrier_def type_non_empty)
done

theorem carrier_member [intro!] :
"x : t \<Longrightarrow> x \<in> carrier t"
apply (auto simp: carrier_def type_non_empty)
done

subsection {* Value Sets *}

definition set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" where
"set_type_rel s t = (\<forall> x \<in> s . x : t)"

notation set_type_rel (infix ":\<subseteq>" 50)

theorem set_type_rel_empty [simp] :
"{} :\<subseteq> t"
apply (auto simp: set_type_rel_def)
done

theorem set_type_rel_insert [simp] :
"(insert x s) :\<subseteq> t \<longleftrightarrow> (x : t \<and> s :\<subseteq> t)"
apply (auto simp: set_type_rel_def)
done

subsection {* Indexable Types *}

definition IdxType :: "'TYPE \<Rightarrow> bool" where
"IdxType t \<longleftrightarrow> IdxSet (carrier t)"

subsection {* Theorems *}

theorem IdxType_IdxSet [simp] :
"\<lbrakk>s :\<subseteq> t; IdxType t\<rbrakk> \<Longrightarrow> IdxSet s"
apply (simp add: IdxType_def)
apply (simp add: set_type_rel_def)
apply (subgoal_tac "s \<subseteq> carrier t")
apply (simp)
apply (auto simp: carrier_def)
done
end

locale BOOL_VALUE = VALUE "type_rel" 
  for     type_rel :: "'VALUE :: BOOL_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) +  
  fixes   BoolType :: "'TYPE"
  assumes IsBool_type: "y : BoolType \<longleftrightarrow> IsBool y"

locale INT_VALUE  = VALUE "type_rel"
  for     type_rel :: "'VALUE :: INT_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) + 
  fixes   IntType :: "'TYPE"
  assumes IsInt_type: "y : IntType \<longleftrightarrow> IsInt y"

locale STRING_VALUE  = VALUE "type_rel"
  for     type_rel :: "'VALUE :: STRING_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) + 
  fixes   StringType :: "'TYPE"
  assumes IsString_type: "y : StringType \<longleftrightarrow> IsString y"

locale BASIC_VALUE = BOOL_VALUE "type_rel" + INT_VALUE "type_rel" + STRING_VALUE "type_rel"
  for type_rel :: "'VALUE :: BASIC_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)

end
