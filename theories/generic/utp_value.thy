(******************************************************************************)
(* Title: utp/generic/utp_value.thy                                           *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Abstract Values *}

theory utp_value
imports "../utp_common"
begin

subsection {* Locale @{term "VALUE"} *}

locale VALUE =
-- {* Typing Relation *}
  fixes type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
-- {* A type must not be empty. *}
  assumes type_non_empty : "\<exists> x . x : t"
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
end