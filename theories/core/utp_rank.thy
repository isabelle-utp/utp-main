theory utp_rank
imports 
  utp_model
  "../alpha/utp_alpha_pred"
begin

class VALUE_RANK = PRE_TYPED_MODEL +
  fixes rank      :: "'a uval \<Rightarrow> nat"
  and   max_rank  :: "'a itself \<Rightarrow> nat"
  assumes rank_type_inj: 
  "\<lbrakk> x1 : t; x2 : t \<rbrakk> \<Longrightarrow> rank x1 = rank x2"
  and rank_sound: "\<forall>n\<le>max_rank TYPE('a). \<exists> x. rank x = n"
begin

definition type_rank :: "'a utype \<Rightarrow> nat" where
"type_rank t = rank (SOME x. x : t)"

definition TRANK :: "nat \<Rightarrow> 'a utype set" where
"TRANK n = {x. type_rank x = n}"

lemma value_rank_type_rank: 
  "x : t \<Longrightarrow> rank x = type_rank t"
  apply (auto simp add: type_rank_def)
  apply (rule someI2, simp)
  apply (metis rank_type_inj)
done

definition RANK :: "nat \<Rightarrow> 'a uval set" where
"RANK n = {x. rank x = n}"

definition pred_rank :: "'a uapred \<Rightarrow> nat" where
"pred_rank P = FMax (type_rank |`| vtype |`| (\<alpha> P))"

definition PRANK :: "nat \<Rightarrow> 'a uapred set" where
"PRANK n = {x. pred_rank x = n}"

end

syntax
  "_MAXRANK"      :: "type => logic"  ("(1MAXRANK/(1'(_')))")

translations
  "MAXRANK('a)" == "CONST max_rank TYPE('a)"

class VALUE_HO = VALUE_RANK +
  assumes rank_inj_func: "\<forall>n<MAXRANK('a). (\<exists> f. dom f = PRANK n \<and> ran f = RANK (n + 1) \<and> inj_on f (dom f))"

end