(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_value.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Abstract Values *}

theory utp_value
imports "../utp_common"
begin

subsection {* Theorem Attributes *}

ML {*
  structure typing =
    Named_Thms (val name = @{binding typing} val description = "typing theorems")
*}

setup typing.setup

subsection {* Locale @{term "VALUE"} *}

locale VALUE =
-- {* Typing Relation *}

  fixes   type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
  and     default  :: "'TYPE \<Rightarrow> 'VALUE"

-- {* A type must not be empty. *}
  assumes default_type [typing]: "(default t) : t"
begin

definition type_rel' :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":\<^sub>l" 50) where
"type_rel' \<equiv> type_rel"

lemma type_non_empty: "\<exists> x::'VALUE. x : (t::'TYPE)"
  apply (rule_tac x="default t" in exI)
  thm default_type
  apply (simp add: default_type)
done

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

(*
subsection {* Subtyping *}


definition subtype :: "'TYPE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix "<:" 65) where
"s <: t \<equiv> \<forall> x. x :\<^sub>l s \<longrightarrow> x :\<^sub>l t"



definition ssubtype :: "'TYPE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix "<:!" 65) where
"ssubtype s t \<equiv> s <: t \<and> \<not> (t <: s)"

lemma subtype_intro[intro]:
  "\<lbrakk> x : s; s <: t \<rbrakk> \<Longrightarrow> x : t"
  by (simp add:subtype_def)

end

sublocale VALUE \<subseteq> preorder "subtype" "ssubtype" 
proof

  show "\<And>x y. x <:! y = (x <: y \<and> \<not> y <: x)"
    by (simp add:ssubtype_def)

  show "\<And>x. x <: x"
    by (simp add:subtype_def)

  show "\<And>x y z. \<lbrakk>x <: y; y <: z\<rbrakk> \<Longrightarrow> x <: z"
    by (simp add:subtype_def)

qed

context VALUE
begin

abbreviation TLeast where "TLeast \<equiv> ord.Least (op <:)"
*)

end

end
