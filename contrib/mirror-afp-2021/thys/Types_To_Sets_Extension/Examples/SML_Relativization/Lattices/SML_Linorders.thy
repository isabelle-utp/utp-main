(* Title: Examples/SML_Relativization/Lattices/SML_Linorders.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about linear orders\<close>
theory SML_Linorders
  imports SML_Semilattices
begin               



subsection\<open>Linear orders\<close>


subsubsection\<open>Definitions and further properties\<close>

locale linorder_ow = order_ow +
  assumes linear: "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w y \<or> y \<le>\<^sub>o\<^sub>w x"
begin

sublocale min: 
  semilattice_order_ow U \<open>(\<lambda>x y. (with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>min\<guillemotright> x y))\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close>
  apply unfold_locales
  subgoal unfolding min.with_def by simp
  subgoal by (metis linear order_trans min.with_def)
  subgoal unfolding min.with_def by (auto dest: linear simp: antisym)
  subgoal unfolding min.with_def by simp
  subgoal unfolding min.with_def by (simp add: eq_iff)
  subgoal unfolding min.with_def by (simp add: less_le)
  done             

sublocale max: 
  semilattice_order_ow U \<open>(\<lambda>x y. (with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>max\<guillemotright> x y))\<close> \<open>(\<ge>\<^sub>o\<^sub>w)\<close> \<open>(>\<^sub>o\<^sub>w)\<close>
  apply unfold_locales
  subgoal unfolding max.with_def by simp
  subgoal by (metis linear order_trans max.with_def)
  subgoal unfolding max.with_def by (auto dest: linear simp: antisym)
  subgoal unfolding max.with_def by simp
  subgoal unfolding max.with_def by (auto dest: linear simp: antisym)
  subgoal unfolding max.with_def by (auto dest: linear simp: less_le_not_le)
  done

end

locale ord_linorder_ow = 
  ord?: ord_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + lo?: linorder_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2
begin

sublocale ord_order_ow ..

end

locale preorder_linorder_ow = 
  po?: preorder_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + lo?: linorder_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2
begin

sublocale preorder_order_ow ..

end

locale order_linorder_ow = 
  order?: order_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + lo?: linorder_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2
begin

sublocale order_pair_ow ..

end

locale linorder_pair_ow = 
  lo\<^sub>1?: linorder_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + lo\<^sub>2?: linorder_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2
begin

sublocale order_linorder_ow ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma linorder_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      (linorder_ow (Collect (Domainp A))) class.linorder"
  unfolding 
    linorder_ow_def class.linorder_def
    linorder_ow_axioms_def class.linorder_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp
  
end


subsubsection\<open>Relativization\<close>

context linorder_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting linorder_ow_axioms
  eliminating through simp
begin

tts_lemma le_less_linear:
  assumes "x \<in> U" and "y \<in> U"
  shows "x \<le>\<^sub>o\<^sub>w y \<or> y <\<^sub>o\<^sub>w x"
  is linorder_class.le_less_linear.

tts_lemma not_less:
  assumes "x \<in> U" and "y \<in> U"
  shows "(\<not> x <\<^sub>o\<^sub>w y) = (y \<le>\<^sub>o\<^sub>w x)"
    is linorder_class.not_less.
    
tts_lemma not_le:
  assumes "x \<in> U" and "y \<in> U"
  shows "(\<not> x \<le>\<^sub>o\<^sub>w y) = (y <\<^sub>o\<^sub>w x)"
    is linorder_class.not_le.

tts_lemma lessThan_minus_lessThan:
  assumes "n \<in> U" and "m \<in> U"
  shows "{..<\<^sub>o\<^sub>wn} - {..<\<^sub>o\<^sub>wm} = (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {m..<n})"
    is linorder_class.lessThan_minus_lessThan.

tts_lemma Ici_subset_Ioi_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "({a..\<^sub>o\<^sub>w} \<subseteq> {b<\<^sub>o\<^sub>w..}) = (b <\<^sub>o\<^sub>w a)"
    is linorder_class.Ici_subset_Ioi_iff.

tts_lemma Iic_subset_Iio_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "({..\<^sub>o\<^sub>wa} \<subseteq> {..<\<^sub>o\<^sub>wb}) = (a <\<^sub>o\<^sub>w b)"
    is linorder_class.Iic_subset_Iio_iff.

tts_lemma leI:
  assumes "x \<in> U" and "y \<in> U" and "\<not> x <\<^sub>o\<^sub>w y"
  shows "y \<le>\<^sub>o\<^sub>w x"
    is linorder_class.leI.

tts_lemma not_le_imp_less:
  assumes "y \<in> U" and "x \<in> U" and "\<not> y \<le>\<^sub>o\<^sub>w x"
  shows "x <\<^sub>o\<^sub>w y"
    is linorder_class.not_le_imp_less.

tts_lemma Int_atMost:
  assumes "a \<in> U" and "b \<in> U"
  shows "{..\<^sub>o\<^sub>wa} \<inter> {..\<^sub>o\<^sub>wb} = {..\<^sub>o\<^sub>wmin a b}"
    is linorder_class.Int_atMost.

tts_lemma lessThan_Int_lessThan:
  assumes "a \<in> U" and "b \<in> U"
  shows "{a<\<^sub>o\<^sub>w..} \<inter> {b<\<^sub>o\<^sub>w..} = {max a b<\<^sub>o\<^sub>w..}"
    is linorder_class.lessThan_Int_lessThan.

tts_lemma greaterThan_Int_greaterThan:
  assumes "a \<in> U" and "b \<in> U"
  shows "{..<\<^sub>o\<^sub>wa} \<inter> {..<\<^sub>o\<^sub>wb} = {..<\<^sub>o\<^sub>wmin a b}"
    is linorder_class.greaterThan_Int_greaterThan.

tts_lemma less_linear:
  assumes "x \<in> U" and "y \<in> U"
  shows "x <\<^sub>o\<^sub>w y \<or> x = y \<or> y <\<^sub>o\<^sub>w x"
    is linorder_class.less_linear.

tts_lemma Int_atLeastAtMostR2:
  assumes "a \<in> U" and "c \<in> U" and "d \<in> U"
  shows "{a..\<^sub>o\<^sub>w} \<inter> {c..\<^sub>o\<^sub>wd} = {max a c..\<^sub>o\<^sub>wd}"
    is linorder_class.Int_atLeastAtMostR2.

tts_lemma Int_atLeastAtMostR1:
  assumes "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "{..\<^sub>o\<^sub>wb} \<inter> {c..\<^sub>o\<^sub>wd} = {c..\<^sub>o\<^sub>wmin b d}"
    is linorder_class.Int_atLeastAtMostR1.

tts_lemma Int_atLeastAtMostL2:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "{a..\<^sub>o\<^sub>wb} \<inter> {c..\<^sub>o\<^sub>w} = {max a c..\<^sub>o\<^sub>wb}"
    is linorder_class.Int_atLeastAtMostL2.

tts_lemma Int_atLeastAtMostL1:
  assumes "a \<in> U" and "b \<in> U" and "d \<in> U"
  shows "{a..\<^sub>o\<^sub>wb} \<inter> {..\<^sub>o\<^sub>wd} = {a..\<^sub>o\<^sub>wmin b d}"
    is linorder_class.Int_atLeastAtMostL1.

tts_lemma neq_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x \<noteq> y) = (x <\<^sub>o\<^sub>w y \<or> y <\<^sub>o\<^sub>w x)"
    is linorder_class.neq_iff.

tts_lemma not_less_iff_gr_or_eq:
  assumes "x \<in> U" and "y \<in> U"
  shows "(\<not> x <\<^sub>o\<^sub>w y) = (y <\<^sub>o\<^sub>w x \<or> x = y)"
    is linorder_class.not_less_iff_gr_or_eq.

tts_lemma max_min_distrib2:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "max a (min b c) = min (max a b) (max a c)"
    is linorder_class.max_min_distrib2.

tts_lemma max_min_distrib1:
  assumes "b \<in> U" and "c \<in> U" and "a \<in> U"
  shows "max (min b c) a = min (max b a) (max c a)"
    is linorder_class.max_min_distrib1.

tts_lemma min_max_distrib2:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "min a (max b c) = max (min a b) (min a c)"
    is linorder_class.min_max_distrib2.

tts_lemma min_max_distrib1:
  assumes "b \<in> U" and "c \<in> U" and "a \<in> U"
  shows "min (max b c) a = max (min b a) (min c a)"
    is linorder_class.min_max_distrib1.

tts_lemma atLeastAtMost_diff_ends:
  assumes "a \<in> U" and "b \<in> U"
  shows "{a..\<^sub>o\<^sub>wb} - {a, b} = {a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb}"
    is linorder_class.atLeastAtMost_diff_ends.

tts_lemma less_max_iff_disj:
  assumes "z \<in> U" and "x \<in> U" and "y \<in> U"
  shows "(z <\<^sub>o\<^sub>w max x y) = (z <\<^sub>o\<^sub>w x \<or> z <\<^sub>o\<^sub>w y)"
    is linorder_class.less_max_iff_disj.

tts_lemma min_less_iff_conj:
  assumes "z \<in> U" and "x \<in> U" and "y \<in> U"
  shows "(z <\<^sub>o\<^sub>w min x y) = (z <\<^sub>o\<^sub>w x \<and> z <\<^sub>o\<^sub>w y)"
    is linorder_class.min_less_iff_conj.

tts_lemma max_less_iff_conj:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "(max x y <\<^sub>o\<^sub>w z) = (x <\<^sub>o\<^sub>w z \<and> y <\<^sub>o\<^sub>w z)"
    is linorder_class.max_less_iff_conj.

tts_lemma min_less_iff_disj:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "(min x y <\<^sub>o\<^sub>w z) = (x <\<^sub>o\<^sub>w z \<or> y <\<^sub>o\<^sub>w z)"
    is linorder_class.min_less_iff_disj.

tts_lemma le_max_iff_disj:
  assumes "z \<in> U" and "x \<in> U" and "y \<in> U"
  shows "(z \<le>\<^sub>o\<^sub>w max x y) = (z \<le>\<^sub>o\<^sub>w x \<or> z \<le>\<^sub>o\<^sub>w y)"
    is linorder_class.le_max_iff_disj.

tts_lemma min_le_iff_disj:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "(min x y \<le>\<^sub>o\<^sub>w z) = (x \<le>\<^sub>o\<^sub>w z \<or> y \<le>\<^sub>o\<^sub>w z)"
    is linorder_class.min_le_iff_disj.

tts_lemma antisym_conv3:
  assumes "y \<in> U" and "x \<in> U" and "\<not> y <\<^sub>o\<^sub>w x"
  shows "(\<not> x <\<^sub>o\<^sub>w y) = (x = y)"
    is linorder_class.antisym_conv3.

tts_lemma Int_atLeastAtMost:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "{a..\<^sub>o\<^sub>wb} \<inter> {c..\<^sub>o\<^sub>wd} = {max a c..\<^sub>o\<^sub>wmin b d}"
    is linorder_class.Int_atLeastAtMost.

tts_lemma Int_atLeastLessThan:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows 
    "(on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b}) \<inter> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {c..<d}) = 
      (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {(max a c)..<(min b d)})"
    is linorder_class.Int_atLeastLessThan.

tts_lemma Int_greaterThanAtMost:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "{a<\<^sub>o\<^sub>w..b} \<inter> {c<\<^sub>o\<^sub>w..d} = {max a c<\<^sub>o\<^sub>w..min b d}"
    is linorder_class.Int_greaterThanAtMost.

tts_lemma Int_greaterThanLessThan:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "{a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb} \<inter> {c<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wd} = {max a c<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wmin b d}"
    is linorder_class.Int_greaterThanLessThan.

tts_lemma le_cases:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>o\<^sub>w y \<Longrightarrow> P" and "y \<le>\<^sub>o\<^sub>w x \<Longrightarrow> P"
  shows P
    is linorder_class.le_cases.

tts_lemma split_max:
  assumes "i \<in> U" and "j \<in> U"
  shows "P (max i j) = ((i \<le>\<^sub>o\<^sub>w j \<longrightarrow> P j) \<and> (\<not> i \<le>\<^sub>o\<^sub>w j \<longrightarrow> P i))"
    is linorder_class.split_max.

tts_lemma split_min:
  assumes "i \<in> U" and "j \<in> U"
  shows "P (min i j) = ((i \<le>\<^sub>o\<^sub>w j \<longrightarrow> P i) \<and> (\<not> i \<le>\<^sub>o\<^sub>w j \<longrightarrow> P j))"
    is linorder_class.split_min.

tts_lemma Ioc_subset_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a<\<^sub>o\<^sub>w..b} \<subseteq> {c<\<^sub>o\<^sub>w..d}) = (b \<le>\<^sub>o\<^sub>w a \<or> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is linorder_class.Ioc_subset_iff.

tts_lemma atLeastLessThan_subset_iff:
  assumes "a \<in> U"
    and "b \<in> U"
    and "c \<in> U"
    and "d \<in> U"
    and "(on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b}) \<subseteq> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {c..<d})"
  shows "b \<le>\<^sub>o\<^sub>w a \<or> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a"
    is linorder_class.atLeastLessThan_subset_iff.

tts_lemma Ioc_inj:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a<\<^sub>o\<^sub>w..b} = {c<\<^sub>o\<^sub>w..d}) = (b \<le>\<^sub>o\<^sub>w a \<and> d \<le>\<^sub>o\<^sub>w c \<or> a = c \<and> b = d)"
    is linorder_class.Ioc_inj.

tts_lemma neqE:
  assumes "x \<in> U"
    and "y \<in> U"
    and "x \<noteq> y"
    and "x <\<^sub>o\<^sub>w y \<Longrightarrow> R"
    and "y <\<^sub>o\<^sub>w x \<Longrightarrow> R"
  shows R
    is linorder_class.neqE.

tts_lemma Ioc_disjoint:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows 
    "({a<\<^sub>o\<^sub>w..b} \<inter> {c<\<^sub>o\<^sub>w..d} = {}) = (b \<le>\<^sub>o\<^sub>w a \<or> d \<le>\<^sub>o\<^sub>w c \<or> b \<le>\<^sub>o\<^sub>w c \<or> d \<le>\<^sub>o\<^sub>w a)"
    is linorder_class.Ioc_disjoint.

tts_lemma linorder_cases:
  assumes "x \<in> U"
    and "y \<in> U"
    and "x <\<^sub>o\<^sub>w y \<Longrightarrow> P"
    and "x = y \<Longrightarrow> P"
    and "y <\<^sub>o\<^sub>w x \<Longrightarrow> P"
  shows P
    is linorder_class.linorder_cases.

tts_lemma le_cases3:
  assumes "x \<in> U"
    and "y \<in> U"
    and "z \<in> U"
    and "\<lbrakk>x \<le>\<^sub>o\<^sub>w y; y \<le>\<^sub>o\<^sub>w z\<rbrakk> \<Longrightarrow> P"
    and "\<lbrakk>y \<le>\<^sub>o\<^sub>w x; x \<le>\<^sub>o\<^sub>w z\<rbrakk> \<Longrightarrow> P"
    and "\<lbrakk>x \<le>\<^sub>o\<^sub>w z; z \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> P"
    and "\<lbrakk>z \<le>\<^sub>o\<^sub>w y; y \<le>\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> P"
    and "\<lbrakk>y \<le>\<^sub>o\<^sub>w z; z \<le>\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> P"
    and "\<lbrakk>z \<le>\<^sub>o\<^sub>w x; x \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> P"
  shows P
    is linorder_class.le_cases3.

end

end

context order_linorder_ow
begin

tts_context
  tts: (?'a to U\<^sub>2) and (?'b to U\<^sub>1)
  rewriting ctr_simps
  substituting order.order_ow_axioms and lo.linorder_ow_axioms
  eliminating through simp
begin


tts_lemma strict_mono_imp_inj_on:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "A \<subseteq> U\<^sub>2"
    and "on U\<^sub>2 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) : \<guillemotleft>strict_mono\<guillemotright> f"
  shows "inj_on f A"
    is linorder_class.strict_mono_imp_inj_on.
    
tts_lemma strict_mono_eq:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "x \<in> U\<^sub>2"
    and "y \<in> U\<^sub>2"
    and "on U\<^sub>2 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) : \<guillemotleft>strict_mono\<guillemotright> f"
  shows "(f x = f y) = (x = y)"
    is linorder_class.strict_mono_eq.

tts_lemma strict_mono_less:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "x \<in> U\<^sub>2"
    and "y \<in> U\<^sub>2"
    and "on U\<^sub>2 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) : \<guillemotleft>strict_mono\<guillemotright> f"
  shows "(f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f y) = (x <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 y)"
    is linorder_class.strict_mono_less.
    
tts_lemma strict_mono_less_eq:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "x \<in> U\<^sub>2"
    and "y \<in> U\<^sub>2"
    and "on U\<^sub>2 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) : \<guillemotleft>strict_mono\<guillemotright> f"
  shows "(f x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f y) = (x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 y)"
    is linorder_class.strict_mono_less_eq.
    
tts_lemma mono_strict_invE:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "x \<in> U\<^sub>2"
    and "y \<in> U\<^sub>2"
    and "on U\<^sub>2 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) : \<guillemotleft>mono\<guillemotright> f"
    and "f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f y"
    and "x <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 y \<Longrightarrow> thesis"
  shows thesis
    is linorder_class.mono_strict_invE.

tts_lemma mono_invE:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "x \<in> U\<^sub>2"
    and "y \<in> U\<^sub>2"
    and "on U\<^sub>2 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) : \<guillemotleft>mono\<guillemotright> f"
    and "f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f y"
    and "x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 y \<Longrightarrow> thesis"
  shows thesis
    is linorder_class.mono_invE.

end
    
end

context linorder_pair_ow
begin

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2)
  rewriting ctr_simps
  substituting lo\<^sub>1.linorder_ow_axioms and lo\<^sub>2.linorder_ow_axioms
  eliminating through simp
begin

tts_lemma max_of_mono:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "m \<in> U\<^sub>1"
    and "n \<in> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
  shows "lo\<^sub>2.max (f m) (f n) = f (lo\<^sub>1.max m n)"
    is linorder_class.max_of_mono.

tts_lemma min_of_mono:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "m \<in> U\<^sub>1"
    and "n \<in> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
  shows "lo\<^sub>2.min (f m) (f n) = f (lo\<^sub>1.min m n)"
    is linorder_class.min_of_mono.

end

end



subsection\<open>Dense linear orders\<close>


subsubsection\<open>Definitions and further properties\<close>

locale dense_linorder_ow = linorder_ow U le ls + dense_order_ow U le ls
  for U :: "'ao set" and le (infix \<open>\<le>\<^sub>o\<^sub>w\<close> 50) and ls (infix \<open><\<^sub>o\<^sub>w\<close> 50)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma dense_linorder_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=))  ===> (=)) 
      (dense_linorder_ow (Collect (Domainp A))) class.dense_linorder"
  unfolding dense_linorder_ow_def class.dense_linorder_def
  apply transfer_prover_start
  apply transfer_step+
  by auto

end


subsubsection\<open>Relativization\<close>

context dense_linorder_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting dense_linorder_ow_axioms
  eliminating through simp
begin

tts_lemma infinite_Icc:
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w b"
  shows "infinite {a..\<^sub>o\<^sub>wb}"
    is dense_linorder_class.infinite_Icc.

tts_lemma infinite_Ico:
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w b"
  shows "infinite (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b})"
    is dense_linorder_class.infinite_Ico.

tts_lemma infinite_Ioc:
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w b"
  shows "infinite {a<\<^sub>o\<^sub>w..b}"
    is dense_linorder_class.infinite_Ioc.

tts_lemma infinite_Ioo:
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w b"
  shows "infinite {a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb}"
    is dense_linorder_class.infinite_Ioo.

tts_lemma atLeastLessThan_subseteq_atLeastAtMost_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows 
    "((on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b}) \<subseteq> {c..\<^sub>o\<^sub>wd}) = 
      (a <\<^sub>o\<^sub>w b \<longrightarrow> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is dense_linorder_class.atLeastLessThan_subseteq_atLeastAtMost_iff.

tts_lemma greaterThanAtMost_subseteq_atLeastAtMost_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a<\<^sub>o\<^sub>w..b} \<subseteq> {c..\<^sub>o\<^sub>wd}) = (a <\<^sub>o\<^sub>w b \<longrightarrow> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is dense_linorder_class.greaterThanAtMost_subseteq_atLeastAtMost_iff.

tts_lemma greaterThanAtMost_subseteq_atLeastLessThan_iff:
  assumes "a \<in> U"
    and "b \<in> U"
    and "c \<in> U"
    and "d \<in> U"
  shows "({a<\<^sub>o\<^sub>w..b} \<subseteq> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {c..<d})) = 
    (a <\<^sub>o\<^sub>w b \<longrightarrow> b <\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is dense_linorder_class.greaterThanAtMost_subseteq_atLeastLessThan_iff.

tts_lemma greaterThanLessThan_subseteq_atLeastAtMost_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb} \<subseteq> {c..\<^sub>o\<^sub>wd}) = (a <\<^sub>o\<^sub>w b \<longrightarrow> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is dense_linorder_class.greaterThanLessThan_subseteq_atLeastAtMost_iff.

tts_lemma greaterThanLessThan_subseteq_atLeastLessThan_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows 
    "({a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb} \<subseteq> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {c..<d})) = 
      (a <\<^sub>o\<^sub>w b \<longrightarrow> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is dense_linorder_class.greaterThanLessThan_subseteq_atLeastLessThan_iff.

tts_lemma greaterThanLessThan_subseteq_greaterThanAtMost_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb} \<subseteq> {c<\<^sub>o\<^sub>w..d}) = (a <\<^sub>o\<^sub>w b \<longrightarrow> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is dense_linorder_class.greaterThanLessThan_subseteq_greaterThanAtMost_iff.

tts_lemma greaterThanLessThan_subseteq_greaterThanLessThan:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb} \<subseteq> {c<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wd}) = (a <\<^sub>o\<^sub>w b \<longrightarrow> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is dense_linorder_class.greaterThanLessThan_subseteq_greaterThanLessThan.

end

end

text\<open>\newpage\<close>

end