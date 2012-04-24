(******************************************************************************)
(* Title: utp/generic/utp_abstract_value.thy                                  *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_abstract_value
imports "../utp_common"
begin

section {* Abstract Values *}

subsection {* Locale @{text "VALUE"} *}

locale VALUE =
-- {* Typing Relation *}
  fixes type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
-- {* Refinement Ordering *}
  fixes value_ref :: "'VALUE \<Rightarrow> 'VALUE \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
-- {* A type must not be empty. *}
  assumes type_non_empty : "\<exists> x . x : t"
-- {* Do we need additional assumptions for the refinement order? *}
begin

subsubsection {* Universe *}

definition universe :: "'VALUE set" where
"universe = UNIV"

subsubsection {* Carrier Set *}

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

subsubsection {* Value Sets *}

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

subsubsection {* Indexable Types *}

definition IdxType :: "'TYPE \<Rightarrow> bool" where
"IdxType t \<longleftrightarrow> IdxSet (carrier t)"

theorem IdxType_IdxSet [simp] :
"s :\<subseteq> t \<and> (IdxType t) \<longrightarrow> (IdxSet s)"
apply (clarify)
apply (simp add: IdxType_def)
apply (simp add: set_type_rel_def)
apply (subgoal_tac "s \<subseteq> carrier t")
apply (simp)
apply (auto simp: carrier_def) [1]
done
end

subsection {* Locale @{text "PROC_VALUE"} *}

text {* This locale introduces additional assumptions for procedure values. *}

locale PROC_VALUE = VALUE "proc_type_rel" "proc_value_ref"
for proc_type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" and
  proc_value_ref :: "'VALUE \<Rightarrow> 'VALUE \<Rightarrow> bool"

subsection {* Theorems *}

theorem PROC_VALUE_inst [intro!] :
"VALUE proc_type_rel \<Longrightarrow> PROC_VALUE proc_type_rel"
apply (simp add: PROC_VALUE_def)
done

subsection {* Proof Experiments *}

print_locale "VALUE"
print_locale "PROC_VALUE"
end
