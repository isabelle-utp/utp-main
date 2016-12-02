subsection {* Definitional UTP universe *}

theory utp_uval
imports utp_dvar
begin

text {* This theory serves to justify the axioms of our axiomatic embedding by providing a model
        for types of cardinality up to $\mathfrak{c}$. *}

class injectable = continuum + typerep

type_synonym utype = "typerep \<times> ucard"

syntax "_UTYPE" :: "type \<Rightarrow> typerep" ("UTYPE'(_')")

translations "UTYPE('a)" \<rightharpoonup> "(TYPEREP('a), UCARD('a))"

definition p_type_rel :: "'a::{typerep, continuum} \<Rightarrow> utype \<Rightarrow> bool" (infix ":" 50) where
"x : t \<longleftrightarrow> (t = UTYPE('a))"

typedef uval = "{((t::typerep, c), x). x \<in> \<U>(c)}"
  apply (auto)
using uinject_card by blast

setup_lifting type_definition_uval

lift_definition InjU :: "'a::injectable \<Rightarrow> uval" 
is "\<lambda> x. (UTYPE('a), uinject x)" by auto

lift_definition ProjU :: "uval \<Rightarrow> 'a::injectable"
is "\<lambda> x. uproject (snd x)" .

lift_definition utype_of :: "uval \<Rightarrow> utype" is "fst" .

definition type_rel :: "uval \<Rightarrow> utype \<Rightarrow> bool" (infix ":\<^sub>u" 50)
where "x :\<^sub>u t = (t = utype_of x)"

lemma InjU_inverse: "ProjU (InjU x) = x"
  by (transfer, auto)

lemma ProjU_inverse: "y :\<^sub>u (TYPEREP('a::injectable), UCARD('a)) \<Longrightarrow> InjU (ProjU y :: 'a) = y"
  apply (simp add: type_rel_def)
  apply (transfer, auto)
done

lemma type_rel: "(InjU x) :\<^sub>u t \<longleftrightarrow> x : t"
  by (simp add: type_rel_def p_type_rel_def, transfer, auto)

lemma types_non_empty: "\<exists> y . y :\<^sub>u t"
  by (auto simp add: type_rel_def, transfer, auto simp add: ex_in_conv ucard_non_empty)

theorem InjU_unique_type: 
  fixes x :: "'a::injectable" and y :: "'b::injectable"
  assumes "InjU x = InjU y"
  shows "UTYPE('a) = UTYPE('b)"
  by (metis InjU.rep_eq assms fst_conv)

end