(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_value.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
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
apply (simp add: carrier_def type_non_empty)
done

theorem carrier_member :
"x : t \<Longrightarrow> x \<in> carrier t"
apply (simp add: carrier_def)
done

theorem carrier_intro :
"(x : t) = (x \<in> carrier t)"
apply (simp add: carrier_def)
done

theorem carrier_elim :
"(x \<in> carrier t) = (x : t)"
apply (simp add: carrier_def)
done

subsection {* Value Sets *}

definition set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" where
"set_type_rel s t = (\<forall> x \<in> s . x : t)"

notation set_type_rel (infix ":\<subseteq>" 50)

theorem set_type_rel_empty [simp] :
"{} :\<subseteq> t"
apply (simp add: set_type_rel_def)
done

theorem set_type_rel_insert [simp] :
"(insert x s) :\<subseteq> t \<longleftrightarrow> (x : t \<and> s :\<subseteq> t)"
apply (simp add: set_type_rel_def)
done
end
end
