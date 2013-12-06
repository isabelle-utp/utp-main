theory utp_rank
imports utp_value
begin

lift_definition FMax :: "('a::linorder) fset \<Rightarrow> 'a" is "Max"
  by (simp)

default_sort VALUE

no_notation
  Set.member  ("op :") and
  Set.member  ("(_/ : _)" [51, 51] 50)

class VALUE_RANK = VALUE +
  fixes type_rank :: "'a UTYPE \<Rightarrow> nat"
  and   max_rank  :: "'a itself \<Rightarrow> nat"
  assumes type_rank_inj: 
  "\<lbrakk> x : t1; x : t2 \<rbrakk> \<Longrightarrow> type_rank t1 = type_rank t2"
  and type_rank_sound: "\<forall>n\<le>max_rank TYPE('a). \<exists> t. type_rank t = n"
begin

definition TRANK :: "nat \<Rightarrow> 'a UTYPE set" where
"TRANK n = {x. type_rank x = n}"

definition rank :: "'a \<Rightarrow> nat" where
"rank x = (if (\<exists> t. x : t) then (type_rank (SOME t. x : t)) else 0)"

lemma value_rank_type_rank: 
  "x : t \<Longrightarrow> rank x = type_rank t"
  apply (auto simp add: rank_def)
  apply (rule someI2, simp)
  apply (metis type_rank_inj)
done

definition RANK :: "nat \<Rightarrow> 'a set" where
"RANK n = {x. rank x = n}"

definition pred_rank :: "'a WF_ALPHA_PREDICATE \<Rightarrow> nat" where
"pred_rank P = FMax (type_rank `\<^sub>f vtype `\<^sub>f (\<alpha> P))"

definition PRANK :: "nat \<Rightarrow> 'a WF_ALPHA_PREDICATE set" where
"PRANK n = {x. pred_rank x = n}"

end

syntax
  "_MAXRANK"      :: "type => logic"  ("(1MAXRANK/(1'(_')))")

translations
  "MAXRANK('a)" == "CONST max_rank TYPE('a)"

class VALUE_HO = VALUE_RANK +
  assumes rank_inj_func: "\<forall>n<MAXRANK('a). (\<exists> f. dom f \<subseteq> PRANK n \<and> ran f \<subseteq> RANK (n + 1))"

end