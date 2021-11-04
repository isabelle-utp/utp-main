(* Title: CTR/CTR.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Infrastructure for the synthesis of the transfer rules and relativized 
constants.
*)


section\<open>\<open>CTR\<close>\<close>
theory CTR
  imports 
    "../UD/UD"
    "HOL-Library.Conditional_Parametricity"
  keywords "ctr_relator" :: thy_defn
    and "ctr" :: thy_defn
    and "trp"
    and "synthesis"
    and "relativization"
    and "hybrid"
    and "parametricity"
begin



subsection\<open>Import\<close>

ML_file "CTR_Relators.ML"
ML_file "CTR_Foundations.ML"
ML_file "CTR_Algorithm.ML"
ML_file "CTR_Conversions.ML"
ML_file "CTR_Relativization.ML"
ML_file "CTR_Parametricity.ML"
ML_file "CTR_Postprocessing.ML"
ML_file "CTR.ML"



subsection\<open>Rewriting\<close>

named_theorems ctr_blank
named_theorems ctr_simps

lemma ctr_simps_pred_fun_top_eq_range[ctr_simps]: 
  "pred_fun top (\<lambda>x. x \<in> R) f = (range f \<subseteq> R)"
  by auto
lemma ctr_simps_pred_prod_eq_cart[ctr_simps]: 
  "pred_prod (\<lambda>x. x \<in> A) (\<lambda>x. x \<in> B) = (\<lambda>x. x \<in> A \<times> B)"
  by auto
lemma ctr_simps_pred_fun_eq_image[ctr_simps]: 
  "pred_fun (\<lambda>x. x \<in> D) (\<lambda>x. x \<in> R) f \<longleftrightarrow> (f ` D \<subseteq> R)"
  by auto
lemma ctr_simps_in_iff[ctr_simps]: "(\<forall>x\<in>A. x \<in> U) \<longleftrightarrow> A \<subseteq> U" by auto
lemma ctr_simps_subset_pow_iff[ctr_simps]: "(\<forall>A\<in>S. A \<subseteq> U) \<longleftrightarrow> S \<subseteq> Pow U" 
  by auto
lemma ctr_simps_subset_pow_iff'[ctr_simps]: 
  "(\<forall>A. A \<in> S \<longrightarrow> A \<subseteq> U) \<longleftrightarrow> S \<subseteq> Pow U" 
  by auto
lemma ctr_simps_subset_pow_iff''[ctr_simps]: "(S \<subseteq> {S. S \<subseteq> U}) \<longleftrightarrow> S \<subseteq> Pow U" 
  by (simp add: subset_eq)
lemma ctr_simps_range_ss_iff[ctr_simps]: "(\<forall>x. f x \<in> U) \<longleftrightarrow> range f \<subseteq> U" 
  by auto
lemma ctr_simps_range_pow_ss_iff[ctr_simps]: "(\<forall>x. f x \<subseteq> U) \<longleftrightarrow> range f \<subseteq> Pow U" 
  by auto
lemma ctr_simps_Ball_def'[ctr_simps]: "(\<forall>x. x \<in> A \<longrightarrow> P x) \<longleftrightarrow> (\<forall>x \<in> A. P x)" 
  by auto
lemma ctr_simps_True_imp[ctr_simps]: "(True \<longrightarrow> A) \<longleftrightarrow> A" by simp
lemma ctr_simps_True_conj[ctr_simps]: "(True \<and> A) \<longleftrightarrow> A" by simp
lemma ctr_simps_conj_True[ctr_simps]: "(A \<and> True) \<longleftrightarrow> A" by simp
lemma ctr_simps_top_True[ctr_simps]: "top A \<longleftrightarrow> True" by auto
lemma ctr_simps_Ball_True[ctr_simps]: "(\<forall>x\<in>U. True) \<longleftrightarrow> True" by auto
lemma ctr_simps_Ball_UNIV[ctr_simps]: "(\<forall>n\<in>UNIV. A n) \<longleftrightarrow> (\<forall>n. A n)" by simp
lemma ctr_simps_Bex_UNIV[ctr_simps]: "(\<exists>n\<in>UNIV. A n) \<longleftrightarrow> (\<exists>n. A n)" by simp
lemma ctr_simps_subset_Pow[ctr_simps]: "{A. A \<subseteq> U} = Pow U" by blast
lemma ctr_simps_mem_Collect_eq[ctr_simps]: "(a \<in> Collect P) = P a"
  by (rule mem_Collect_eq)
lemma ctr_simps_relation_top_empty_eq[ctr_simps]: "(\<lambda>x. x \<in> UNIV) = top" 
  by auto
lemma ctr_simps_pred_fun_eq[ctr_simps]: 
  "pred_fun A B = (\<lambda>f. \<forall>x. A x \<longrightarrow> B (f x))" 
  by simp
lemma ctr_simps_subset_eq_sym[ctr_simps]: "(\<forall>x\<in>A. x \<in> B) \<longleftrightarrow> (A \<subseteq> B)" by auto
lemma ctr_simps_UNIV_I[ctr_simps]: "x \<in> UNIV" by simp
lemma ctr_simps_UNIV_def[ctr_simps]: "{x. True} = UNIV" by simp
lemma ctr_simps_conj_commute[ctr_simps]: "(P \<and> Q) \<longleftrightarrow> (Q \<and> P)" by auto
lemma ctr_simps_conj_absorb[ctr_simps]: "(A \<and> A) \<longleftrightarrow> A" by simp
lemma ctr_simps_conj_left_absorb[ctr_simps]: "(A \<and> A \<and> B) \<longleftrightarrow> (A \<and> B)" by simp
lemma ctr_simps_inf_idem[ctr_simps]: "inf a a = (a::'a::semilattice_inf)" 
  by simp
lemma ctr_simps_sup_idem[ctr_simps]: "sup a a = (a::'a::semilattice_sup)" 
  by simp
lemma ctr_simps_inf_assoc[ctr_simps]: 
  "inf (inf a b) c = inf (a::'a::semilattice_inf) (inf b c)"
  by (auto simp: semilattice_inf_class.inf.assoc)
lemma ctr_simps_sup_assoc[ctr_simps]:
  "sup (sup a b) c = sup (a::'a::semilattice_sup) (sup b c)"
  by (auto simp: semilattice_sup_class.sup.assoc)
lemma ctr_simps_Collect_mem_eq[ctr_simps]: "{x. x \<in> U} = U" by simp



subsection\<open>tts relators\<close>

ctr_relator rel_set
ctr_relator rel_filter

end