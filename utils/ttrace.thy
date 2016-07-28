section {* Timed traces *}

theory ttrace
  imports 
  Real_Vector_Spaces
  Positive
  "Library_extra/Map_Extra" 
  "Library_extra/List_extra" 
  "Library_extra/Monoid_extra" 
  "~~/src/HOL/Multivariate_Analysis/Topology_Euclidean_Space"
begin

lemma dom_shift_plus: 
  fixes n :: "'a::ring"
  shows "dom (\<lambda> x. f (x + n)) = {x - n | x. x \<in> dom f}"
  by (auto simp add: dom_def, force)

lemma dom_shift_minus: 
  fixes n :: "'a::ring"
  shows "dom (\<lambda> x. f (x - n)) = op + n ` dom f"
  by (simp add: dom_def image_Collect, force)

lemma plus_image_atLeastLessThan:
  fixes m n k :: "real"
  shows "op + k ` {m..<n} = {m+k..<n+k}"
  by (auto, metis add.commute atLeastLessThan_iff diff_add_cancel diff_less_eq imageI le_diff_eq)

definition Sup' :: "real set \<Rightarrow> real" where
"Sup' A = (if (A = {}) then 0 else Sup A)"

lemma Sup'_empty [simp]: "Sup' {} = 0"
  by (simp add: Sup'_def)

lemma Sup'_interval [simp]: "Sup' {0..<m} = (if (m > 0) then m else 0)"
  by (simp add: Sup'_def)

subsection {* Contiguous functions *}

typedef 'a cgf = 
  "{f :: real \<rightharpoonup> 'a. (\<exists> i. i \<ge> 0 \<and> dom(f) = {0..<i})}"
  by (rule_tac x="Map.empty" in exI, auto)

setup_lifting type_definition_cgf

lift_definition cgf_apply :: "'a cgf \<Rightarrow> preal \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>C") is "\<lambda> f x. the (f x)" .
lift_definition cgf_dom :: "'a cgf \<Rightarrow> preal set" ("dom\<^sub>C") is dom by (auto)
lift_definition cgf_end :: "'a cgf \<Rightarrow> preal" ("end\<^sub>C") is "\<lambda> f. if (dom(f) = {}) then 0 else Sup(dom(f))" 
  using less_eq_real_def by auto

instantiation cgf :: (type) zero
begin
  lift_definition zero_cgf :: "'a cgf" is Map.empty by (auto)
instance ..
end

abbreviation (input) cgf_empty :: "'a cgf" ("[]\<^sub>C") where "[]\<^sub>C \<equiv> 0"

instantiation cgf :: (type) plus
begin

lift_definition plus_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf"
is "\<lambda> f g. (\<lambda> x. if (x < Sup'(dom(f))) then f x else g (x - Sup'(dom(f))))"
  apply (auto simp add: dom_if)
  apply (rename_tac f g i j)
  apply (simp add: dom_shift_minus plus_image_atLeastLessThan)
  apply (rule_tac x="j + i" in exI)
  apply (auto)
done

instance ..

end

abbreviation (input) cgf_cat :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf" (infixl "@\<^sub>C" 85) where "xs @\<^sub>C ys \<equiv> xs + ys"

lemma cgf_cat_left_unit [simp]: "[]\<^sub>C @\<^sub>C t = t"
  by (transfer, rule ext, auto, metis (full_types) atLeastLessThan_iff domIff not_le)

lemma cgf_cat_right_unit [simp]: "t @\<^sub>C []\<^sub>C = t"
  apply (transfer, auto)
  apply (rename_tac t i)
  apply (rule ext)
  apply (auto)
  apply (metis (full_types) atLeastLessThan_iff domIff)
done

lemma map_eqI:
  "\<lbrakk> dom f = dom g; \<forall> x\<in>dom(f). the(f x) = the(g x) \<rbrakk> \<Longrightarrow> f = g"
  by (metis domIff map_le_antisym map_le_def option.expand)

lemma cgf_eqI: "\<lbrakk> end\<^sub>C f = end\<^sub>C g; \<forall> x<end\<^sub>C g. \<langle>f\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C x \<rbrakk> \<Longrightarrow> f = g"
  apply (transfer)
  apply (rename_tac f g)
  apply (auto)[1]
  apply (case_tac "g = Map.empty")
  apply (simp_all)
  using less_eq_real_def apply auto[1]
  apply (case_tac "f = Map.empty")
  apply (auto)
  apply (rule map_eqI)
  apply (metis atLeastLessThan_empty_iff2 cSup_atLeastLessThan dom_eq_empty_conv not_less)
  apply (metis (mono_tags) atLeastLessThan_empty atLeastLessThan_iff cSup_atLeastLessThan dom_eq_empty_conv less_eq_real_def)
done

lemma cgf_end_ge_0 [simp]: "end\<^sub>C(f) \<ge> 0"
  by (transfer, auto simp add: less_eq_real_def)

lemma cgf_end_empty [simp]: "end\<^sub>C([]\<^sub>C) = 0"
  by (transfer, simp)

lemma cgf_end_0_iff: "end\<^sub>C(f) = 0 \<longleftrightarrow> f = []\<^sub>C"
  by (transfer, force simp add: antisym_conv2)

lemma atLeastLessThan_inter_nzero [simp]: "{0..<i::real} \<inter> {x. \<not> x < 0} = {0..<i}" 
  by auto

lemma atLeastLessThan_inter_nless [simp]: "{i..<j::real} \<inter> {x. \<not> x < i} = {i..<j}" 
  by auto

lemma atLeastLessThan_inter_less [simp]: "(j::real) \<ge> i \<Longrightarrow> {0..<i} \<inter> {x. x < j} = {0..<i}"
  by (auto)

lemma atLeastLessThan_inter_greater [simp]: "(j::real) \<le> i \<Longrightarrow> {0..<i} \<inter> {x. x < j} = {0..<j}"
  by (auto)

lemma atLeastLessThan_union_disj [simp]: "\<lbrakk> 0 \<le> i; i \<le> j \<rbrakk> \<Longrightarrow> {0..<i::real} \<union> {i..<j} = {0..<j}"
  by (auto)

lemma cgf_end_cat: "end\<^sub>C(f @\<^sub>C g) = end\<^sub>C(f)+end\<^sub>C(g)"
  apply (case_tac "f = []\<^sub>C")
  apply (simp)
  apply (transfer)
  apply (clarsimp simp add: dom_if dom_shift_minus plus_image_atLeastLessThan)
  using less_eq_real_def apply auto
done  

lemma cgf_cat_ext_first: "x < end\<^sub>C f \<Longrightarrow> \<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>f\<rangle>\<^sub>C x"
  by (transfer, auto, metis (mono_tags) cSup_atLeastLessThan le_less_trans less_eq_real_def)

lemma cgf_cat_ext_last: "x \<ge> end\<^sub>C f \<Longrightarrow> \<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C (x - end\<^sub>C f)"
  by (transfer, auto, metis (mono_tags, hide_lams) atLeastLessThan_empty_iff2 cSup_atLeastLessThan domIff empty_iff less_le_not_le)

lemma cgf_cat_assoc: "(f @\<^sub>C g) @\<^sub>C h = f @\<^sub>C (g @\<^sub>C h)"
proof (rule cgf_eqI, simp_all add: cgf_end_cat add.assoc, clarify)
  fix x
  assume x: "x < end\<^sub>C f + (end\<^sub>C g + end\<^sub>C h)" 
  show "\<langle>f @\<^sub>C g @\<^sub>C h\<rangle>\<^sub>C x = \<langle>f @\<^sub>C (g @\<^sub>C h)\<rangle>\<^sub>C x"
  proof (cases "x < end\<^sub>C f")
    case True thus ?thesis
      by (metis (mono_tags, hide_lams) add.right_neutral add_less_cancel_left cgf_cat_ext_first cgf_end_cat cgf_end_ge_0 le_less_trans not_le)
  next
    case False 
    hence x_gef: "x \<ge> end\<^sub>C f"
      by auto
    thus ?thesis
    proof (cases "x < end\<^sub>C f+end\<^sub>C g")
      case True thus ?thesis
        apply (simp add: add.commute add_less_imp_less_left cgf_cat_ext_first cgf_cat_ext_last cgf_end_cat x_gef)
        apply (subst cgf_cat_ext_first)
        apply (metis add_less_imp_less_left le_add_diff_inverse x_gef)
        apply (simp)
      done
    next
      case False 
      hence x_gefg: "x \<ge> end\<^sub>C f+end\<^sub>C g"
        by auto
      thus ?thesis
        by (simp add: add.commute cgf_cat_ext_last cgf_end_cat diff_diff_add add_le_imp_le_diff x_gef)
    qed
  qed
qed

instantiation cgf :: (type) order
begin
  lift_definition less_eq_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> bool" is 
  "op \<subseteq>\<^sub>m" .
  definition less_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> bool" where
  "less_cgf x y = (x \<le> y \<and> \<not> y \<le> x)"
instance
  apply (intro_classes)
  apply (simp add: less_cgf_def)
  apply (transfer, auto)
  apply (transfer, auto intro: map_le_trans)
  apply (transfer, auto simp add: map_le_antisym)
done
end

abbreviation (input) cgf_prefix :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> bool" (infix "\<subseteq>\<^sub>C" 50)
where "f \<subseteq>\<^sub>C g \<equiv> f \<le> g"

lemma cgf_prefix_least [simp]: "[]\<^sub>C \<le> f"
  by (transfer, auto)

lemma cgf_prefix_cat [simp]: "f \<le> f @\<^sub>C g"
  apply (transfer, auto simp add: map_le_def)
  using less_eq_real_def apply auto
done

lemma cgf_sub_end:
  "f \<le> g \<Longrightarrow> end\<^sub>C f \<le> end\<^sub>C g"
  apply (cases "dom\<^sub>C(f) = {}")
  apply (transfer, auto)
  apply (metis atLeastLessThan_empty_iff2 cSup_atLeastLessThan dom_eq_empty_conv)
  apply (transfer, auto)
  apply (rename_tac x f g i j y)
  apply (subgoal_tac "f \<noteq> Map.empty")
  apply (subgoal_tac "g \<noteq> Map.empty")
  apply (auto)
  apply (metis (mono_tags, hide_lams) atLeastLessThan_empty_iff2 cSup_atLeastLessThan dom_eq_empty_conv ivl_subset map_le_implies_dom_le order_trans)
  using map_le_antisym map_le_empty apply blast
done

lemma cgf_prefix_dom:
  "f \<subseteq>\<^sub>C g \<Longrightarrow> dom\<^sub>C(f) \<subseteq> dom\<^sub>C(g)"
  by (transfer, auto simp add: map_le_def, metis domI)

instantiation cgf :: (type) minus
begin

lift_definition minus_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf" is
"\<lambda> f g. if (g \<subseteq>\<^sub>m f) then (\<lambda> x. if (x \<ge> 0 \<and> x < (Sup'(dom f) - Sup'(dom g))) 
                               then f (x + Sup'(dom g)) else None) 
        else Map.empty"
  apply (auto simp add: dom_shift_plus dom_if)
  apply (rename_tac f g i j)
  apply (rule_tac x="i - j" in exI)
  apply (auto)
  using map_le_implies_dom_le apply fastforce
  apply (metis add.commute add_less_cancel_left diff_add_cancel le_diff_eq less_eq_real_def less_iff_diff_less_0 less_trans not_less order_refl order_trans)
  apply (rename_tac f i)  
  apply (rule_tac x="i" in exI, auto)
done 

instance ..
end

lemma cgf_minus_nprefix [simp]: "\<not> g \<le> f \<Longrightarrow> f - g = []\<^sub>C"
  by (transfer, simp)

lemma cgf_minus_self [simp]: "f - f = []\<^sub>C"
  by (transfer, rule ext, auto)

lemma cgf_minus_empty [simp]: "f - []\<^sub>C = f"
  apply (transfer, auto intro!:ext)
  using domIff apply fastforce+
done

lemma cgf_cat_minus [simp]: "f @\<^sub>C g - f = g"
  apply (transfer)
  apply (rename_tac f g)
  apply (case_tac "dom f = {}")
  apply (auto simp add: map_le_def dom_if)
  apply (rule ext)
  using domIff apply fastforce
  apply (force)
  apply (rename_tac f g i j)
  apply (simp add: dom_shift_minus plus_image_atLeastLessThan)
  apply (subgoal_tac "{0..<i} \<inter> {x. x < i} \<union> {i..<j + i} \<inter> {x. \<not> x < i} = {0..<j+i}")
  apply (simp)
  apply (rule ext)
  using domIff apply fastforce
  apply (auto)
  using less_eq_real_def apply auto
  apply force
done

lemma cgf_cat_minus_prefix:
  "f \<le> g \<Longrightarrow> g = f @\<^sub>C (g - f)"
  apply (case_tac "f = []\<^sub>C")
  apply (simp)
  apply (transfer, auto simp add: dom_if)
  apply (rule ext)
  apply (auto simp add: map_le_antisym)
  apply (metis atLeastLessThan_iff domIff map_le_def)
  using map_le_implies_dom_le apply fastforce
done

lemma dom_range_nempty [simp]: "\<lbrakk> dom(f) = {0..<(i::real)}; f \<noteq> Map.empty \<rbrakk> \<Longrightarrow> i > 0"
  by (auto)
  
lemma cgf_prefix_iff: "f \<le> g \<longleftrightarrow> (\<exists> h. g = f @\<^sub>C h)"
  apply (auto)
  apply (rule_tac x="g - f" in exI)
  apply (simp add: cgf_cat_minus_prefix)
done

lemma cgf_apply_minus [simp]: "f \<le> g \<Longrightarrow> \<langle>g - f\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C (x + end\<^sub>C(f))"
  apply (transfer, auto)
  apply (metis (full_types) atLeastLessThan_iff domIff less_eq_real_def)
  apply (metis (full_types) atLeastLessThan_empty_iff2 atLeastLessThan_iff domIff less_diff_eq)
done

lemma cgf_end_minus: "g \<le> f \<Longrightarrow> end\<^sub>C(f-g) = end\<^sub>C(f)-end\<^sub>C(g)"
  by (auto simp add: cgf_prefix_iff cgf_end_cat)

lemma cgf_left_mono_iff: "f @\<^sub>C g \<le> f @\<^sub>C h \<longleftrightarrow> g \<le> h"
  apply (auto simp add: cgf_prefix_iff)
  apply (metis cgf_cat_assoc cgf_cat_minus)
  apply (metis cgf_cat_assoc)
done

lemma list_concat_minus_list_concat: "(f @\<^sub>C g) - (f @\<^sub>C h) = g - h"
  apply (case_tac "f = []\<^sub>C")
  apply (simp)
  apply (case_tac "\<not> h \<le> g")
  apply (simp_all add: cgf_minus_nprefix cgf_left_mono_iff)
  apply (transfer, auto simp add: dom_if dom_shift_minus plus_image_atLeastLessThan map_le_def)
done

instance cgf :: (type) ordered_cancel_monoid_diff
  apply (intro_classes)
  apply (simp_all add: cgf_cat_assoc list_concat_minus_list_concat cgf_prefix_iff)
done

(*
locale pc_interval =
  fixes I :: "real list" and f :: "'a::topological_space cgf"
  assumes I_range: "set(I) \<subseteq> {0 .. end\<^sub>C f}"
  and I_bounds: "{0, end\<^sub>C f} \<subseteq> set(I)"
  and I_sorted [simp]: "sorted I"
  and I_distinct [simp]: "distinct I"
  and continuous_segments [intro]: "\<And> i. i < length(I) - 1 \<Longrightarrow> continuous_on {I!i ..< I!(Suc i)} \<langle>f\<rangle>\<^sub>C"
begin

  lemma I_length [simp]: "length(I) > 0"
    using I_bounds by auto

  lemma ne_f_I_length [simp]: "f \<noteq> []\<^sub>C \<Longrightarrow> length(I) > Suc 0"
    by (metis I_bounds I_length Suc_lessI cgf_end_0_iff in_set_conv_nth insert_subset less_Suc0)

  lemma I_hd [simp]: "hd(I) = 0"
    by (metis I_bounds I_range I_sorted atLeastAtMost_iff atLeastLessThan_empty atLeastLessThan_empty_iff contra_subsetD empty_iff hd_in_set insert_subset less_eq_real_def list.exhaust_sel list.set(1) sorted_Cons tl_element)

  lemma I_last: "last(I) = end\<^sub>C(f)"
    by (metis I_bounds I_range I_sorted atLeastAtMost_iff dual_order.antisym empty_iff insert_subset last_in_set list.set(1) sorted_last subsetCE)
    
  lemma tl_I_ge_0 [simp]: "x \<in> set (tl I) \<Longrightarrow> x > 0"
    by (metis I_distinct I_hd I_length I_sorted distinct.simps(2) hd_Cons_tl length_greater_0_conv less_eq_real_def sorted_Cons)

  lemma I_z [simp]: "0 \<in> set(I)"
    using I_bounds by blast

  lemma I_nz [simp]: "x \<in> set(I) \<Longrightarrow> 0 \<le> x"
    using I_range atLeastAtMost_iff by blast

  lemma nth_I_nz: "i < length I \<Longrightarrow> 0 \<le> I!i"
    by simp

  lemma I_le_end [simp]: "x \<in> set(I) \<Longrightarrow> x \<le> end\<^sub>C(f)"
    using I_last I_sorted sorted_last by fastforce


end

definition piecewise_continuous :: "'a::topological_space cgf \<Rightarrow> bool" where
"piecewise_continuous f = (\<exists> I. pc_interval I f)"

lemma sorted_map: "\<lbrakk> sorted xs; mono f \<rbrakk> \<Longrightarrow> sorted (map f xs)"
  by (simp add: monoD sorted_equals_nth_mono)

(*
lemma "\<lbrakk> i \<ge> end\<^sub>C(f); i < end\<^sub>C(f)+end\<^sub>C(g) \<rbrakk> \<Longrightarrow> \<langle>f @\<^sub>C g\<rangle>\<^sub>C i = \<langle>g\<rangle>\<^sub>C (i - end\<^sub>C(f))"
*)


lemma continuous_on_linear: 
  fixes A :: "real set"
  shows "continuous_on A (\<lambda> x. m*x + a)"
proof (clarsimp simp add: continuous_on_def)
  fix x
  show "((\<lambda>x. m * x + a) \<longlongrightarrow> m * x + a) (at x within A)"
    by (force intro: tendsto_add[of "(\<lambda>x. m * x)" "m * x" "at x within A" "\<lambda>_. a" a, simplified] tendsto_mult)
qed

lemma continuous_on_shift:
  fixes f :: "real \<Rightarrow> 'b::topological_space"
  assumes "continuous_on A f"
  shows "continuous_on {x + y | x. x \<in> A} (\<lambda> x. f (x - y))" 
proof -
  have "((\<lambda>x. x - y) ` {x + y |x. x \<in> A}) = A"
    by (force simp add: image_Collect)
  moreover have "continuous_on {x + y |x. x \<in> A} (\<lambda>x. x - y)"
    using continuous_on_linear[of "{x + y |x. x \<in> A}" 1 "- y"] by (simp)
  ultimately show ?thesis 
  using continuous_on_compose[of "{x + y | x. x \<in> A}" "\<lambda> x. x - y" f]
    by (simp add: assms)
qed

lemma continuous_on_cgf_cat_right:
  assumes "0 \<le> i" "continuous_on {i+end\<^sub>C(f)..<j+end\<^sub>C(f)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
  shows "continuous_on {i..<j} \<langle>g\<rangle>\<^sub>C"
proof -
  have "{x - end\<^sub>C f |x. i + end\<^sub>C f \<le> x \<and> x < j + end\<^sub>C f} = {i..<j}"
    by (auto, metis add_diff_cancel add_le_cancel_right add_less_cancel_right)
  hence "continuous_on {i..<j} (\<lambda>x. \<langle>f @\<^sub>C g\<rangle>\<^sub>C (x + end\<^sub>C f))"
    using continuous_on_shift[of _ _ "- end\<^sub>C f",OF assms(2), simplified] by (simp)
  moreover from assms(1) have "continuous_on {i..<j} (\<lambda>x. \<langle>f @\<^sub>C g\<rangle>\<^sub>C (x + end\<^sub>C f)) = ?thesis"
    by (rule_tac continuous_on_cong, auto simp add: cgf_cat_ext_last)
  ultimately show ?thesis
    by simp
qed

lemma continuous_on_cgf_cat_last:
  assumes "end\<^sub>C(f) \<le> i" "continuous_on {i-end\<^sub>C(f)..<j-end\<^sub>C(f)} \<langle>g\<rangle>\<^sub>C"
  shows "continuous_on {i..<j} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
proof -
  have "{x + end\<^sub>C f |x. i - end\<^sub>C f \<le> x \<and> x < j - end\<^sub>C f} = {i..<j}"
    by (auto, metis add_diff_cancel diff_add_eq diff_right_mono diff_strict_right_mono)
  hence "continuous_on {i..<j} (\<lambda> x. \<langle>g\<rangle>\<^sub>C (x-end\<^sub>C(f)))"
    using continuous_on_shift[of _ _ "end\<^sub>C f",OF assms(2)] by simp
  moreover from assms(1) have "continuous_on {i..<j} (\<lambda>x. \<langle>g\<rangle>\<^sub>C (x - end\<^sub>C f)) = ?thesis"
    by (rule_tac continuous_on_cong, auto intro: continuous_on_cong simp add: cgf_cat_ext_last)
  ultimately show ?thesis by blast
qed

lemma dropWhile_sorted_le_above:
  "\<lbrakk> sorted xs; x \<in> set (dropWhile (\<lambda> x. x \<le> n) xs) \<rbrakk> \<Longrightarrow> x > n"
  apply (induct xs)
  apply (auto)
  apply (rename_tac a xs)
  apply (case_tac "a \<le> n")
  apply (simp_all)
  using sorted_Cons apply blast
  apply (meson dual_order.trans not_less sorted_Cons)
done

lemma piecewise_continuous_empty [simp]: "piecewise_continuous []\<^sub>C"
  by (auto simp add: piecewise_continuous_def, rule_tac x="[0]" in exI, simp add: pc_interval_def cgf_end_empty)

lemma piecewise_continuous_cat_right:
  assumes "piecewise_continuous (f @\<^sub>C g)"
  shows "piecewise_continuous g"
proof (cases "g = []\<^sub>C")
  case True thus ?thesis by (simp add: assms)
next
  case False note egnz = this
  from assms obtain I where "pc_interval I (f @\<^sub>C g)"
    by (auto simp add: piecewise_continuous_def)
  then interpret I: pc_interval I "(f @\<^sub>C g)" .
  obtain I\<^sub>1 I\<^sub>2 where I_split: "I = I\<^sub>1 @ I\<^sub>2" "set(I\<^sub>1) \<subseteq> {0..end\<^sub>C f}" "set(I\<^sub>2) \<subseteq> {end\<^sub>C f<..end\<^sub>C f+end\<^sub>C g}"
  proof -
    have "I = takeWhile (\<lambda> x. x \<le> end\<^sub>C f) I @ dropWhile (\<lambda> x. x \<le> end\<^sub>C f) I"
      by simp
    moreover have "set(takeWhile (\<lambda> x. x \<le> end\<^sub>C f) I) \<subseteq> {0..end\<^sub>C f}"
      by (auto, (meson I.I_nz set_takeWhileD)+)
    moreover have "set(dropWhile (\<lambda> x. x \<le> end\<^sub>C f) I) \<subseteq> {end\<^sub>C f<..end\<^sub>C f+end\<^sub>C g}"
      by (auto intro!: dropWhile_sorted_le_above[of I], metis I.I_le_end cgf_end_cat set_dropWhileD) 
    ultimately show ?thesis using that by blast
  qed
  have efg: "end\<^sub>C f + end\<^sub>C g \<in> set I\<^sub>2"
    by (metis I.I_bounds I_split(1) I_split(2) Un_iff add.right_neutral add_left_cancel atLeastAtMost_iff cgf_end_0_iff cgf_end_cat cgf_prefix_cat cgf_sub_end contra_subsetD dual_order.antisym egnz insertCI set_append)

  have zI\<^sub>1: "0 \<in> set(I\<^sub>1)"
    using I.I_z I_split(1) I_split(3) linorder_not_less by force

  let ?I\<^sub>2' = "0 # map (\<lambda> x. x - end\<^sub>C f) I\<^sub>2"
  have "pc_interval ?I\<^sub>2' g"
  proof 
    show "set(?I\<^sub>2') \<subseteq> {0 .. end\<^sub>C g}"
      using I_split(3) by auto
    show "{0, end\<^sub>C g} \<subseteq> set(?I\<^sub>2')"
      using efg by force
    show sorted_I\<^sub>2': "sorted ?I\<^sub>2'"
    proof -
      have "sorted I\<^sub>2"
        using I.I_sorted I_split(1) sorted_append by blast
      thus ?thesis
        using I_split(3) by (force intro:sorted_map monoI simp add: sorted_Cons sorted_map)
    qed
    show "distinct ?I\<^sub>2'"
    proof -
      have "distinct I\<^sub>2"
        using I.I_distinct by (simp add: I_split(1))
      thus ?thesis
        using I_split(3) greaterThanAtMost_iff by (auto simp add: distinct_map inj_onI)
    qed
  show "\<And> i. i < length(?I\<^sub>2') - 1 \<Longrightarrow> continuous_on {?I\<^sub>2'!i ..< ?I\<^sub>2'!(Suc i)} \<langle>g\<rangle>\<^sub>C"
  proof simp
    fix i
    assume i:"i < length I\<^sub>2"
    hence "(0 # map (\<lambda>x. x - end\<^sub>C f) I\<^sub>2) ! i + end\<^sub>C f = (end\<^sub>C f # I\<^sub>2) ! i"
      by (case_tac "i = 0", auto)

    moreover have "continuous_on {end\<^sub>C f..<I\<^sub>2 ! 0} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
    proof -
      have "I\<^sub>2 ! 0 = I ! Suc (length I\<^sub>1 - 1)"
        by (auto simp add: I_split nth_append, metis I.I_z I_split(1) I_split(3) Suc_pred append.simps(1) cgf_end_ge_0 greaterThanAtMost_iff le_0_eq length_greater_0_conv not_less subsetCE zero_less_diff)
      moreover have "I ! (length I\<^sub>1 - 1) \<le> end\<^sub>C f"
        apply (auto simp add: I_split nth_append)
        using I_split(2) atLeastAtMost_iff nth_mem apply blast
        apply (meson diff_Suc_less length_pos_if_in_set zI\<^sub>1)
      done
      ultimately have "{end\<^sub>C f..<I\<^sub>2 ! 0} \<subseteq> {I ! (length I\<^sub>1 - 1)..<I ! Suc (length I\<^sub>1 - 1)}"
        by (simp)
      moreover have "continuous_on {I ! (length I\<^sub>1 - 1)..<I ! Suc (length I\<^sub>1 - 1)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
        by (metis (no_types, lifting) I.I_length I.continuous_segments I_split(1) One_nat_def Suc_diff_1 Suc_eq_plus1 Suc_leI add.commute cancel_comm_monoid_add_class.diff_cancel efg le_less_linear length_append length_pos_if_in_set less_diff_conv2 less_not_sym zI\<^sub>1)
      ultimately show ?thesis
        using continuous_on_subset by blast
    qed

    moreover have "i > 0 \<Longrightarrow> continuous_on {I\<^sub>2 ! (i - Suc 0)..<I\<^sub>2 ! i} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
    proof auto
      assume iz: "i > 0"
      have "I\<^sub>2 ! (i - Suc 0) = I ! (i - Suc 0 + length I\<^sub>1)"
        by (auto simp add: I_split nth_append)
      moreover from iz have "I\<^sub>2 ! i = I ! Suc (i - Suc 0 + length I\<^sub>1)"
        by (auto simp add: I_split nth_append)
      moreover from i iz 
      have "continuous_on {I ! (i - Suc 0 + length I\<^sub>1)..<I ! Suc (i - Suc 0 + length I\<^sub>1)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
        by (rule_tac I.continuous_segments, auto simp add: I_split)
      ultimately show ?thesis
        by simp
    qed

    ultimately show "continuous_on {(0 # map (\<lambda>x. x - end\<^sub>C f) I\<^sub>2) ! i..<I\<^sub>2 ! i - end\<^sub>C f} \<langle>g\<rangle>\<^sub>C"
      apply (simp)
      apply (rule continuous_on_cgf_cat_right[of _ f])
      apply (auto)
      apply (metis i add.right_neutral add_Suc_right le0 length_map less_SucI list.size(4) nth_Cons_0 sorted_I\<^sub>2' sorted_nth_mono)
      apply (case_tac "i = 0")
      apply (simp_all)
    done
  qed
qed

thus ?thesis
  using piecewise_continuous_def by blast
qed

lemma piecewise_continuous_cat:
  assumes "piecewise_continuous f" "piecewise_continuous g"
  shows "piecewise_continuous (f @\<^sub>C g)"
proof (cases "g = []\<^sub>C")
  case True thus ?thesis by (simp add: assms)
next
  case False note gne = this
  hence gegz: "end\<^sub>C(g) > 0"
    using cgf_end_0_iff cgf_end_ge_0 less_eq_real_def by auto 
  from assms obtain I\<^sub>1 where "pc_interval I\<^sub>1 f"
    by (auto simp add: piecewise_continuous_def)
  then interpret I\<^sub>1: pc_interval I\<^sub>1 f .
  from assms obtain I\<^sub>2 where "pc_interval I\<^sub>2 g"
    by (auto simp add: piecewise_continuous_def)
  then interpret I\<^sub>2: pc_interval I\<^sub>2 g .
  let ?I = "I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)"

  have "ran\<^sub>l ?I \<subseteq> {0..end\<^sub>C f+end\<^sub>C g}"
    using I\<^sub>2.I_length list.set_sel(2) by (force simp add: add_increasing2 less_imp_le)

  moreover have "end\<^sub>C f+end\<^sub>C g \<in> set(?I)"
    using I\<^sub>2.I_bounds cgf_end_0_iff gne tl_element by fastforce 

  moreover have "sorted ?I"
    by (auto intro!:sorted_map monoI simp add: sorted_append sorted_tl)
       (metis I\<^sub>1.I_le_end I\<^sub>2.tl_I_ge_0 add.commute le_add_same_cancel2 less_eq_real_def order_trans)

  moreover have "distinct ?I"
    apply (auto simp add: distinct_map distinct_tl inj_onI)
    using I\<^sub>1.I_le_end I\<^sub>2.tl_I_ge_0 by fastforce

  moreover have "\<And> i. i < length(?I) - 1 \<Longrightarrow> continuous_on {?I!i ..< ?I!(Suc i)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
  proof (simp)
    fix i
    assume i:"i < length I\<^sub>1 + (length I\<^sub>2 - Suc 0) - Suc 0" 
    thus "continuous_on {?I!i ..< ?I!(Suc i)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
    proof (cases "i < length I\<^sub>1 - 1")
      case True 
      hence Si: "Suc i < length I\<^sub>1"
        by (simp add: gne)

      hence "\<And> x. x \<in> {I\<^sub>1 ! i..<I\<^sub>1 ! Suc i} \<Longrightarrow> \<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>f\<rangle>\<^sub>C x"
        using I\<^sub>1.I_le_end less_le_trans nth_mem by (force simp add: cgf_cat_ext_first)

      with Si show ?thesis
        by (metis I\<^sub>1.continuous_segments Suc_lessD True continuous_on_cong nth_append)
    next
      case False 
      moreover hence il: "i \<ge> length I\<^sub>1 - 1"
        by auto
      moreover hence "?I ! i = (I\<^sub>2 ! (i - (length I\<^sub>1 - Suc 0))) + end\<^sub>C(f)"
      proof (cases "i < length I\<^sub>1")
        case True
        moreover with il have "i = length I\<^sub>1 - Suc 0"
          by auto
        moreover have "I\<^sub>1 ! (length I\<^sub>1 - Suc 0) = last(I\<^sub>1)"
          using I\<^sub>1.I_length last_conv_nth by force
        moreover have "I\<^sub>2 ! 0 = hd(I\<^sub>2)"
          using I\<^sub>2.I_length hd_conv_nth by force
        ultimately show ?thesis
          by (auto simp add: nth_append I\<^sub>1.I_last)
      next
        case False
        moreover hence "i \<ge> length I\<^sub>1"
          by auto
        moreover hence "(i - length I\<^sub>1) < length (tl I\<^sub>2)"
          using i by auto
        ultimately show ?thesis
          by (auto simp add: nth_append nth_tl, metis I\<^sub>1.I_length One_nat_def Suc_diff_eq_diff_pred Suc_diff_le)
      qed

      moreover have "(i - (length I\<^sub>1 - Suc 0)) < length I\<^sub>2"
        using False i by linarith
        
      moreover have "(Suc i - length I\<^sub>1) < length (tl I\<^sub>2)"
        by (metis False I\<^sub>1.I_length I\<^sub>2.I_length Nat.add_diff_assoc2 One_nat_def Suc_diff_eq_diff_pred Suc_leI Suc_pred add_diff_inverse_nat calculation(4) i length_tl less_antisym nat_neq_iff)

      moreover have "tl I\<^sub>2 ! (Suc i - length I\<^sub>1) = I\<^sub>2 ! Suc (i - (length I\<^sub>1 - Suc 0))"
        by (metis I\<^sub>1.I_length One_nat_def Suc_diff_eq_diff_pred calculation(5) nth_tl)
        
      ultimately show ?thesis
        apply (auto simp add: nth_append)
        apply (rule continuous_on_cgf_cat_last)
        apply (auto)
        apply (rule I\<^sub>2.continuous_segments)
        apply (auto)
        apply (metis I\<^sub>1.I_length One_nat_def Suc_diff_eq_diff_pred)
      done
    qed
  qed

  ultimately have "pc_interval ?I (f @\<^sub>C g)"
    by (unfold_locales, simp_all add: cgf_end_cat)

  thus ?thesis
    using piecewise_continuous_def by blast

qed

lemma piecewise_continuous_minus:
  assumes "piecewise_continuous f" "piecewise_continuous g" "f \<le> g"
  shows "piecewise_continuous (g - f)"
proof -
  obtain h where "g = f @\<^sub>C h"
    using assms(3) cgf_prefix_iff by blast
  with assms show ?thesis
    using piecewise_continuous_cat_right by auto
qed

lemma continuous_on_cgf_prefix:
  "\<lbrakk> f \<subseteq>\<^sub>C g; 0 \<le> i; i < j; j \<le> end\<^sub>C f; continuous_on {i..<j} \<langle>g\<rangle>\<^sub>C \<rbrakk> \<Longrightarrow> continuous_on {i..<j} \<langle>f\<rangle>\<^sub>C"
  apply (transfer, auto)
  apply (rename_tac f g i j i' j')
  apply (case_tac "f = Map.empty")
  apply (auto simp add: map_le_def)
  apply (subgoal_tac "continuous_on {i..<j} (\<lambda>x. the (f x)) = continuous_on {i..<j} (\<lambda>x. the (g x))")
  apply (simp)
  apply (rule continuous_on_cong)
  apply (simp)
  apply (metis atLeastLessThan_iff cSup_atLeastLessThan domIff le_cases le_less_trans not_less_iff_gr_or_eq)
done 

typedef (overloaded) 'a::topological_space ttrace = 
  "{f :: 'a cgf. piecewise_continuous f}"
  by (rule_tac x="[]\<^sub>C" in exI, simp)

setup_lifting type_definition_ttrace

lift_definition tt_empty :: "'a::topological_space ttrace" ("[]\<^sub>t") is cgf_empty
  by simp

lift_definition tt_cat :: "'a::topological_space ttrace \<Rightarrow> 'a ttrace \<Rightarrow> 'a ttrace" (infixl "@\<^sub>t" 85)
is "op @\<^sub>C" by (simp add: piecewise_continuous_cat)

lemma tt_cat_left_zero: "[]\<^sub>t @\<^sub>t t = t"
  by (transfer, simp)

lemma tt_cat_right_zero: "t @\<^sub>t []\<^sub>t = t"
  by (transfer, simp)

lemma tt_cat_assoc: "(f @\<^sub>t g) @\<^sub>t h = f @\<^sub>t (g @\<^sub>t h)"
  by (transfer, simp add: cgf_cat_assoc)

instantiation ttrace :: (topological_space) order
begin

lift_definition less_eq_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> bool" is "op \<le>" .
lift_definition less_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> bool" is "op <" .

instance by (intro_classes, (transfer, simp add: less_cgf_def)+)

end

lemma ttrace_min: "[]\<^sub>t \<le> t"
  by (transfer, simp)

instantiation ttrace :: (topological_space) minus
begin

  lift_definition minus_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> 'a ttrace" 
  is "\<lambda> s t. if (t \<le> s) then s - t else s"
    by (auto, simp add: piecewise_continuous_minus)

  instance ..

end

lemma tt_self_cancel [simp]: "t - t = []\<^sub>t"
  by (transfer, simp)

lemma tt_minus_empty [simp]: "t - []\<^sub>t = t"
  by (transfer, simp)

lemma tt_append_cancel [simp]: "(x @\<^sub>t y) - x = y"
  by (transfer, auto)
*)
text {* Hide implementation details for cgfs and ttraces *}
  
lifting_update cgf.lifting
lifting_forget cgf.lifting

(*
lifting_update ttrace.lifting
lifting_forget ttrace.lifting
*)

end