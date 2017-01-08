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

abbreviation rshift :: "('a::ring \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixr "\<ggreater>" 66) where
"rshift f n \<equiv> (\<lambda> x. f (x - n))"

abbreviation lshift :: "'a \<Rightarrow> ('a::ring \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixl "\<lless>" 65) where
"lshift n f \<equiv> (\<lambda> x. f (x + n))"

lemma dom_shift_plus: 
  fixes n :: "'a::ring"
  shows "dom (n \<lless> f) = {x - n | x. x \<in> dom f}"
  by (auto simp add: dom_def, force)

lemma dom_shift_minus: 
  fixes n :: "'a::ring"
  shows "dom (f \<ggreater> n) = op + n ` dom f"
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

lemma map_eqI:
  "\<lbrakk> dom f = dom g; \<forall> x\<in>dom(f). the(f x) = the(g x) \<rbrakk> \<Longrightarrow> f = g"
  by (metis domIff map_le_antisym map_le_def option.expand)

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

lemma map_restrict_dom_compl: "f |` (- dom f) = Map.empty"
  by (metis dom_eq_empty_conv dom_restrict inf_compl_bot)

lemma restrict_map_neg_disj:
  "dom(f) \<inter> A = {} \<Longrightarrow> f |` (- A) = f"
  by (auto simp add: restrict_map_def, rule ext, auto, metis disjoint_iff_not_equal domIff)

lemma map_plus_restrict_dist: "(f ++ g) |` A = (f |` A) ++ (g |` A)"
  by (auto simp add: restrict_map_def map_add_def)

subsection {* Contiguous functions *}

typedef 'a cgf = 
  "{f :: real \<rightharpoonup> 'a. (\<exists> i. i \<ge> 0 \<and> dom(f) = {0..<i})}"
  by (rule_tac x="Map.empty" in exI, auto)

setup_lifting type_definition_cgf

lift_definition cgf_apply :: "'a cgf \<Rightarrow> real \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>C") is "\<lambda> f x. the (f x)" .
lift_definition cgf_dom :: "'a cgf \<Rightarrow> real set" ("dom\<^sub>C") is dom .
lift_definition cgf_end :: "'a cgf \<Rightarrow> real" ("end\<^sub>C") is "\<lambda> f. if (dom(f) = {}) then 0 else Sup(dom(f))" .
lift_definition cgf_map :: "(real \<times> 'a \<Rightarrow> 'b) \<Rightarrow> 'a cgf \<Rightarrow> 'b cgf" ("map\<^sub>C") 
  is "\<lambda> f g x. if (x \<in> dom(g)) then Some (f (x, the(g(x)))) else None" 
  by (auto simp add: dom_if)

abbreviation "map'\<^sub>C f \<equiv> cgf_map (\<lambda> (i, x). f x)"

lift_definition cgf_restrict :: "'a cgf \<Rightarrow> real \<Rightarrow> 'a cgf" (infix "\<restriction>\<^sub>C" 85)
is "\<lambda> f i. f |` {0..<i}" 
  by (auto simp add: min_def, blast, metis atLeastLessThan_empty_iff2 less_eq_real_def less_irrefl) 

lift_definition cgf_force :: "'a cgf \<Rightarrow> real \<Rightarrow> 'a cgf" (infix "!\<^sub>C" 85)
is "\<lambda> f i x. if (0 \<le> x \<and> x < i) then Some(the(f(x))) else None"
  apply (rename_tac f n)
  apply (case_tac "n \<ge> 0")
  apply (auto simp add: dom_if)
done

instantiation cgf :: (type) zero
begin
  lift_definition zero_cgf :: "'a cgf" is Map.empty by (auto)
instance ..
end

abbreviation (input) cgf_empty :: "'a cgf" ("[]\<^sub>C") where "[]\<^sub>C \<equiv> 0"

instantiation cgf :: (type) plus
begin

lift_definition plus_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf"
is "\<lambda> f g. (g \<ggreater> Sup'(dom(f))) ++ f"
 apply (auto simp add: dom_shift_minus plus_image_atLeastLessThan)
 apply (rename_tac f g i j)
 apply (rule_tac x="i + j" in exI)
 apply (auto simp add: image_Collect)
done

instance ..

end

abbreviation (input) cgf_cat :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf" (infixl "@\<^sub>C" 85) where "xs @\<^sub>C ys \<equiv> xs + ys"

lemma cgf_cat_left_unit [simp]: "[]\<^sub>C @\<^sub>C t = t"
  by (transfer, simp)

lemma cgf_cat_right_unit [simp]: "t @\<^sub>C []\<^sub>C = t"
  by (transfer, auto)

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


lemma cgf_end_cat: "end\<^sub>C(f @\<^sub>C g) = end\<^sub>C(f)+end\<^sub>C(g)"
  apply (case_tac "f = []\<^sub>C")
  apply (simp)
  apply (transfer)
  apply (auto simp add: dom_shift_minus plus_image_atLeastLessThan)
  using less_eq_real_def apply auto
done

lemma cgf_cat_ext_first: 
  assumes "x < end\<^sub>C f" 
  shows "\<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>f\<rangle>\<^sub>C x"
proof (cases "f = []\<^sub>C")
  case True with assms show ?thesis
    by (transfer, auto, metis atLeastLessThan_iff domIff less_le_not_le)
next
  case False with assms show ?thesis
    apply (transfer, auto, subst map_add_comm)
    apply (auto)
    apply (metis atLeastLessThan_iff domI less_eq_real_def less_iff_diff_less_0 not_less_iff_gr_or_eq)
    apply (metis atLeastLessThan_iff domIff less_iff_diff_less_0 less_le_not_le map_add_def option.case(1))
  done
       
qed

lemma cgf_cat_ext_last: "x \<ge> end\<^sub>C f \<Longrightarrow> \<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C (x - end\<^sub>C f)"
  by (transfer, auto simp add: map_add_dom_app_simps(3))

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
        by (simp add: add_less_imp_less_left cgf_cat_ext_first cgf_cat_ext_last cgf_end_cat x_gef)
    next
      case False 
      hence x_gefg: "x \<ge> end\<^sub>C f+end\<^sub>C g"
        by auto
      thus ?thesis
        by (simp add: add.commute cgf_cat_ext_last cgf_end_cat diff_diff_add add_le_imp_le_diff x_gef)
    qed
  qed
qed

lemma cgf_end_map [simp]: "end\<^sub>C (map\<^sub>C f g) = end\<^sub>C g"
  by (transfer, auto simp add: dom_if)

lemma cgf_dom_empty [simp]: "dom\<^sub>C([]\<^sub>C) = {}"
  by (transfer, simp)

lemma cgf_dom: "dom\<^sub>C(f) = {0..<end\<^sub>C f}"
  apply (cases "f = []\<^sub>C")
  apply (auto)
  apply (transfer, auto)
  apply (transfer, auto)
  using less_eq_real_def apply auto[1]
  apply (transfer, auto)
  using less_eq_real_def apply auto
done

lemma cgf_restrict_empty [simp]: "[]\<^sub>C \<restriction>\<^sub>C n = []\<^sub>C"
  by (transfer, simp)

lemma cgf_end_restrict [simp]: "\<lbrakk> 0 \<le> n; n \<le> end\<^sub>C f \<rbrakk> \<Longrightarrow> end\<^sub>C (f \<restriction>\<^sub>C n) = n"
  apply (transfer, auto)
  apply (metis (mono_tags) atLeastLessThan_empty_iff2 cSup_atLeastLessThan domI empty_iff le_less_trans min.absorb_iff2 not_less_iff_gr_or_eq)
done

lemma cgf_end_force [simp]: "n \<ge> 0 \<Longrightarrow> end\<^sub>C (f !\<^sub>C n) = n"
  apply (transfer, auto simp add: dom_if)
  apply (rename_tac n f i x)
  apply (subgoal_tac "{x. 0 \<le> x \<and> x < n} = {0..<n}")
  apply (auto)
done

lemma cgf_map_indep:
  "end\<^sub>C f = end\<^sub>C g \<Longrightarrow> map\<^sub>C (\<lambda>(i, x). \<langle>g\<rangle>\<^sub>C i) f = g"
  apply (transfer, auto, rule ext, auto)
  apply (metis atLeastLessThan_iff cSup_atLeastLessThan domIff le_less_trans not_less_iff_gr_or_eq option.collapse)
  apply fastforce
  apply (metis (no_types) atLeastLessThan_iff cSup_atLeastLessThan domIff min.absorb_iff2 min_def not_less)
done

lemma cgf_restrict_map [simp]: "(map\<^sub>C f g) \<restriction>\<^sub>C n = map\<^sub>C f (g \<restriction>\<^sub>C n)"
  apply (transfer, auto simp add: restrict_map_def, rule ext, auto simp add: domD)
  apply (metis atLeastLessThan_iff domI option.distinct(1))
done

lemma cgf_restrict_restrict [simp]: "(g \<restriction>\<^sub>C m) \<restriction>\<^sub>C n = g \<restriction>\<^sub>C (min m n)"
  apply (auto simp add: min_def)
  apply (transfer, simp add: min.absorb_iff2 min.commute)
  apply (transfer, auto simp add: min_def)
done

lemma cgf_map_empty [simp]:
  "map\<^sub>C f []\<^sub>C = []\<^sub>C"
  by (transfer, simp)

lemma cgf_map_apply [simp]:
  assumes "0 \<le> x" "x < end\<^sub>C(g)"
  shows "\<langle>map\<^sub>C f g\<rangle>\<^sub>C x = f (x, \<langle>g\<rangle>\<^sub>C x)"
proof -
  have "x \<in> dom\<^sub>C(g)"
    using assms cgf_dom by fastforce
  thus ?thesis
    by (transfer, auto simp add: dom_if)
qed

lemma cgf_map_map: "map\<^sub>C f (map\<^sub>C g h) = map\<^sub>C (\<lambda> (i, x). f (i, g (i, x))) h"
  by (transfer, auto simp add: dom_if)

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
  by (transfer, auto simp add: map_le_def) 

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

lemma cgf_restrict_le: "t \<restriction>\<^sub>C n \<le> t"
  by (transfer, auto simp add: map_le_def)

lemma cgf_restrict_less: "\<lbrakk> 0 \<le> n ; n < end\<^sub>C(t) \<rbrakk> \<Longrightarrow> t \<restriction>\<^sub>C n < t"
  by (metis cgf_end_restrict cgf_restrict_le dual_order.strict_iff_order)

instantiation cgf :: (type) minus
begin

lift_definition minus_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf" is
"\<lambda> f g. if (g \<subseteq>\<^sub>m f) then Sup' (dom g) \<lless> (f |` (- dom(g))) else Map.empty"
proof (auto simp add: dom_shift_plus)
  fix f g  :: "real \<rightharpoonup> 'a" and i j
  assume a: "0 \<le> i" "dom f = {0..<i}" "dom g = {0..<j}" "g \<subseteq>\<^sub>m f" "0 < j"
  hence i: "i \<ge> j"
    using map_le_implies_dom_le by fastforce
  with a have "{x - j |x. 0 \<le> x \<and> x < i \<and> \<not> x < j} = {0..<i-j}"
    by (auto, rename_tac x, rule_tac x="x + j" in exI, simp)
  moreover with i have "i-j \<ge> 0"
    by simp
   
  ultimately show "\<exists>k\<ge>0. {x - j |x. 0 \<le> x \<and> x < i \<and> (0 \<le> x \<longrightarrow> \<not> x < j)} = {0..<k}"
    by (rule_tac x="i-j" in exI, auto)
next
  fix f  :: "real \<rightharpoonup> 'a" and i
  assume "0 \<le> i" "dom f = {0..<i}"
  thus "\<exists> j\<ge>0. {x. 0 \<le> x \<and> x < i} = {0..<j}"
    by (rule_tac x="i" in exI, auto)
qed

instance ..
end

lemma cgf_minus_nprefix [simp]: "\<not> g \<le> f \<Longrightarrow> f - g = []\<^sub>C"
  by (transfer, simp)
  
lemma cgf_minus_self [simp]: "f - f = []\<^sub>C"
  by (transfer, simp add: map_restrict_dom_compl)

lemma cgf_minus_empty [simp]: "f - []\<^sub>C = f"
  by (transfer, simp)

lemma cgf_cat_minus [simp]: "f @\<^sub>C g - f = g"
  apply (transfer, auto simp add: map_plus_restrict_dist map_restrict_dom_compl)
  apply (subst restrict_map_neg_disj)
  apply (auto)
  apply (metis atLeastLessThan_iff domI less_eq_real_def less_iff_diff_less_0 not_less_iff_gr_or_eq)
done

lemma cgf_cat_minus_prefix:
  "f \<le> g \<Longrightarrow> g = f @\<^sub>C (g - f)"
  apply (case_tac "f = []\<^sub>C")
  apply (simp)
  apply (transfer, auto simp add: dom_if)
  apply (metis map_add_empty map_add_le_mapI map_add_restrict map_le_antisym map_le_iff_map_add_commute map_le_map_add map_le_trans)
done

lemma dom_range_nempty [simp]: "\<lbrakk> dom(f) = {0..<(i::real)}; f \<noteq> Map.empty \<rbrakk> \<Longrightarrow> i > 0"
  by (auto)
  
lemma cgf_prefix_iff: "f \<le> g \<longleftrightarrow> (\<exists> h. g = f @\<^sub>C h)"
  apply (auto)
  apply (rule_tac x="g - f" in exI)
  apply (simp add: cgf_cat_minus_prefix)
done

lemma cgf_apply_minus [simp]: "\<lbrakk> 0 \<le> x; f \<le> g \<rbrakk> \<Longrightarrow> \<langle>g - f\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C (x + end\<^sub>C(f))"
  by (transfer, auto)

lemma cgf_end_minus: "g \<le> f \<Longrightarrow> end\<^sub>C(f-g) = end\<^sub>C(f)-end\<^sub>C(g)"
  by (auto simp add: cgf_prefix_iff cgf_end_cat)

lemma cgf_left_mono_iff: "f @\<^sub>C g \<le> f @\<^sub>C h \<longleftrightarrow> g \<le> h"
  apply (auto simp add: cgf_prefix_iff)
  apply (metis cgf_cat_assoc cgf_cat_minus)
  apply (metis cgf_cat_assoc)
done

lemma map_le_plus_eq_iff:
  "f ++ h \<subseteq>\<^sub>m g ++ h \<longleftrightarrow> (f |` (-dom h)) \<subseteq>\<^sub>m (g |` (-dom h))"
  apply (auto simp add: map_le_def)
  apply (metis (mono_tags) UnCI domI map_add_def not_None_eq option.simps(4))
  apply (metis (no_types, lifting) ComplI IntI domI map_add_dom_app_simps(1) map_add_dom_app_simps(3))
done

lemma list_concat_minus_list_concat: "(f @\<^sub>C g) - (f @\<^sub>C h) = g - h"
proof (cases "h \<le> g")
  case False
  thus ?thesis
    by (simp add: cgf_minus_nprefix cgf_left_mono_iff)
next
  case True
  then obtain h' where "g = h @\<^sub>C h'"
    using cgf_prefix_iff by blast
  thus ?thesis
    by (simp, metis cgf_cat_assoc cgf_cat_minus)
qed

instance cgf :: (type) ordered_cancel_monoid_diff
  apply (intro_classes)
  apply (simp_all add: cgf_cat_assoc list_concat_minus_list_concat cgf_prefix_iff)
done

subsection {* Piecewise continuous and convergent functions *}

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

locale pc_cvg_interval = pc_interval +
  -- {* The following assumption requires that each continuous segment also converges to a limit *}
  assumes cvg_segments [intro]: 
    "\<And> i. i < length(I) - 1 \<Longrightarrow> \<exists> L. (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I!(Suc i)) within {I!i ..< I!(Suc i)})"

definition piecewise_continuous :: "'a::topological_space cgf \<Rightarrow> bool" where
"piecewise_continuous f = (\<exists> I. pc_interval I f)"

definition piecewise_convergent :: "'a::topological_space cgf \<Rightarrow> bool" where
"piecewise_convergent f = (\<exists> I. pc_cvg_interval I f)"

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

lemma continuous_on_cgf_cat_left:
  assumes "j \<le> end\<^sub>C f" "continuous_on {i..<j} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
  shows "continuous_on {i..<j} \<langle>f\<rangle>\<^sub>C"
proof -
  have "continuous_on {i..<j} \<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longleftrightarrow> continuous_on {i..<j} \<langle>f\<rangle>\<^sub>C"
    by (rule continuous_on_cong, auto, meson assms(1) cgf_cat_ext_first le_less_trans not_le)
  thus ?thesis
    using assms by blast
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

lemma piecewise_convergent_empty [simp]: "piecewise_convergent []\<^sub>C"
   by (auto simp add: piecewise_convergent_def, rule_tac x="[0]" in exI, simp add: pc_interval_def pc_cvg_interval_def pc_cvg_interval_axioms_def cgf_end_empty)

lemma set_dropWhile_le:
  "sorted xs \<Longrightarrow> set (dropWhile (\<lambda> x. x \<le> n) xs) = {x\<in>set xs. x > n}"
  apply (induct xs)
  apply (simp)
  apply (rename_tac x xs)
  apply (subgoal_tac "sorted xs")
  apply (simp)
  apply (safe)
  apply (simp_all)
  apply (meson not_less order_trans sorted_Cons)
  using sorted_Cons apply auto
done

definition "left_pc_interval n I = (takeWhile (\<lambda> x. x < n) I) @ [n]"

definition "right_pc_interval n I = 0 # map (\<lambda> x. x - n) (dropWhile (\<lambda> x. x \<le> n) I)"

thm set_takeWhileD

lemma set_takeWhile_less_sorted: 
  "\<lbrakk> sorted I; x \<in> set I; x < n \<rbrakk> \<Longrightarrow> x \<in> set (takeWhile (\<lambda>x. x < n) I)"
proof (induct I arbitrary: x)
  case Nil thus ?case
    by (simp)
next
  case (Cons a I) thus ?case
    by (auto, (meson le_less_trans sorted_Cons)+)
qed

lemma set_left_pc_interval:
  "sorted I \<Longrightarrow> set (left_pc_interval n I) = insert n {x |x. x \<in> ran\<^sub>l I \<and> n > x}"
  by (auto dest: set_takeWhileD simp add: left_pc_interval_def set_dropWhile_le image_Collect set_takeWhile_less_sorted)

lemma set_right_pc_interval:
  "sorted I \<Longrightarrow> set (right_pc_interval n I) = insert 0 {x - n |x. x \<in> ran\<^sub>l I \<and> n < x}"
  by (simp add: right_pc_interval_def set_dropWhile_le image_Collect)

lemma nth_le_takeWhile_ord: "\<lbrakk> sorted xs; i \<ge> length (takeWhile (\<lambda> x. x \<le> n) xs); i < length xs \<rbrakk> \<Longrightarrow> n \<le> xs ! i"
  apply (induct xs arbitrary: i, auto)
  apply (rename_tac x xs i)
  apply (case_tac "x \<le> n")
  apply (auto simp add: sorted_Cons)
  apply (metis One_nat_def Suc_eq_plus1 le_less_linear le_less_trans less_imp_le list.size(4) nth_mem set_ConsD)
done

lemma length_takeWhile_less:
  "\<lbrakk> a \<in> set xs; \<not> P a \<rbrakk> \<Longrightarrow> length (takeWhile P xs) < length xs"
  by (metis in_set_conv_nth length_takeWhile_le nat_neq_iff not_less set_takeWhileD takeWhile_nth)

lemma nth_length_takeWhile_less:
  "\<lbrakk> sorted xs; distinct xs; (\<exists> a \<in> set xs. a \<ge> n) \<rbrakk> \<Longrightarrow> xs ! length (takeWhile (\<lambda>x. x < n) xs) \<ge> n"
  apply (induct xs, auto)
  using sorted_Cons by blast

lemma pc_interval_left:
  assumes "pc_interval I (f @\<^sub>C g)"
  shows "pc_interval (left_pc_interval (end\<^sub>C f) I) f"
proof
  interpret I: pc_interval I "(f @\<^sub>C g)" by (simp add: assms)
  show "set (left_pc_interval (end\<^sub>C f) I) \<subseteq> {0..end\<^sub>C f}"
    by (auto simp add: set_left_pc_interval)
  show "{0, end\<^sub>C f} \<subseteq> ran\<^sub>l (left_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: set_left_pc_interval dual_order.strict_iff_order)
  show "sorted (left_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: left_pc_interval_def sorted_takeWhile sorted_append, meson less_eq_real_def set_takeWhileD)
  show "distinct (left_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: left_pc_interval_def, meson less_irrefl set_takeWhileD)
  show "\<And>i. i < length (left_pc_interval (end\<^sub>C f) I) - 1 \<Longrightarrow>
         continuous_on {left_pc_interval (end\<^sub>C f) I ! i..<left_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>f\<rangle>\<^sub>C"
  proof (rule continuous_on_cgf_cat_left[of _ _ _ g])
    fix i
    assume i:"i < length (left_pc_interval (end\<^sub>C f) I) - 1"
    hence ef_nz: "end\<^sub>C f > 0"
      by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, metis I.nth_I_nz le_less_trans length_takeWhile_le not_less nth_mem set_takeWhileD takeWhile_nth)
    from i show "left_pc_interval (end\<^sub>C f) I ! Suc i \<le> end\<^sub>C f"
      by (auto simp add: left_pc_interval_def nth_append, meson less_eq_real_def nth_mem set_takeWhileD)
    from i show "continuous_on {left_pc_interval (end\<^sub>C f) I ! i..<left_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>f + g\<rangle>\<^sub>C"
    proof (cases "Suc i < length (takeWhile (\<lambda>x. x < end\<^sub>C f) I)")
      case True
      with i show ?thesis
        by (auto simp add: left_pc_interval_def nth_append, metis I.I_length I.continuous_segments One_nat_def Suc_lessD Suc_less_eq Suc_pred length_takeWhile_le less_le_trans takeWhile_nth)
    next
      case False
      let ?l = "length (takeWhile (\<lambda>x. x < end\<^sub>C f) I)"
      from False i have i_def: "i = ?l - 1"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
      have lI: "last I \<ge> end\<^sub>C f"
        by (simp add: I.I_last cgf_sub_end)
      have ltI: "?l > 0"
          by (metis One_nat_def add.left_neutral cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc i left_pc_interval_def length_append length_greater_0_conv less_nat_zero_code list.size(3) list.size(4))
      hence I_ge_end:"I ! Suc (?l - 1) \<ge> end\<^sub>C f"
      proof -
        from lI have "I ! length (takeWhile (\<lambda>x. x < end\<^sub>C f) I) \<ge> end\<^sub>C f"
          by (rule_tac nth_length_takeWhile_less, auto, metis I.I_z empty_iff last_in_set list.set(1))
        with ltI show ?thesis
          by simp
      qed
      have c: "continuous_on {I ! (?l - 1)..<I ! Suc(?l - 1)} \<langle>f + g\<rangle>\<^sub>C"
      proof -
        have "length (takeWhile (\<lambda>x. x < end\<^sub>C f) I) < length I"
          using I.I_length lI last_in_set length_takeWhile_less by fastforce
        thus ?thesis
          using ltI by (rule_tac I.continuous_segments, auto, linarith)
      qed
      have "continuous_on {I ! (?l - 1)..<end\<^sub>C f} \<langle>f + g\<rangle>\<^sub>C"
        by (rule continuous_on_subset[OF c], auto, metis I_ge_end One_nat_def)
      with False i i_def show ?thesis
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
    qed
  qed
qed
    
lemma pc_interval_right:
  assumes "pc_interval I (f @\<^sub>C g)"
  shows "pc_interval (right_pc_interval (end\<^sub>C f) I) g"
proof
  interpret I: pc_interval I "(f @\<^sub>C g)" by (simp add: assms)
  obtain I' where I': "I = 0 # I'" "sorted I'" "distinct I'"
    by (metis I.I_distinct I.I_hd I.I_length I.I_sorted distinct.simps(2) hd_Cons_tl length_greater_0_conv sorted_Cons)
  show "set (right_pc_interval (end\<^sub>C f) I) \<subseteq> {0..end\<^sub>C g}"
    by (auto simp add: set_right_pc_interval, metis I.I_le_end cancel_ab_semigroup_add_class.add_diff_cancel_left' cgf_end_cat diff_strict_right_mono less_eq_real_def)
  show "{0, end\<^sub>C g} \<subseteq> set (right_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: set_right_pc_interval, metis I.I_last I.I_z cancel_ab_semigroup_add_class.add_diff_cancel_left' cgf_end_cat cgf_end_ge_0 diff_gt_0_iff_gt last_in_set length_greater_0_conv length_pos_if_in_set less_eq_real_def)
  show "sorted (right_pc_interval (end\<^sub>C f) I)"
    apply (auto intro!:sorted_map sorted_dropWhile simp add: right_pc_interval_def sorted_Cons mono_def)
    using I.I_sorted dropWhile_sorted_le_above less_eq_real_def apply blast
  done
  show "distinct (right_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: right_pc_interval_def set_dropWhile_le distinct_map inj_onI)
  show "\<And>i. i < length (right_pc_interval (end\<^sub>C f) I) - 1 \<Longrightarrow>
         continuous_on {right_pc_interval (end\<^sub>C f) I ! i..<right_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>g\<rangle>\<^sub>C"
  proof -
    fix i
    assume i: "i < length (right_pc_interval (end\<^sub>C f) I) - 1"
    hence egnz: "end\<^sub>C g > 0"
      by (simp add: right_pc_interval_def, metis I.I_le_end I.I_sorted add.right_neutral cgf_end_0_iff cgf_end_ge_0 dropWhile_sorted_le_above less_eq_real_def not_less nth_mem set_dropWhileD)      
    let ?i' = "length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I)"
    show "continuous_on {right_pc_interval (end\<^sub>C f) I ! i..<right_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>g\<rangle>\<^sub>C"
    proof (cases "i = 0")
      case True 
      have "?i' < length I"
        by (metis I.I_last I.I_length add.right_neutral add_left_cancel append_Nil2 egnz cgf_end_cat cgf_prefix_cat cgf_sub_end last_in_set le_less_trans length_0_conv length_append length_takeWhile_le not_less_iff_gr_or_eq set_takeWhileD takeWhile_dropWhile_id)
      moreover have "?i' > 0"
        by (metis I.I_sorted I.I_z Un_iff cgf_end_ge_0 dropWhile_sorted_le_above empty_iff length_greater_0_conv list.set(1) not_less set_append takeWhile_dropWhile_id)
      moreover have "continuous_on {I ! (?i'-1)..<I ! Suc(?i'-1)} \<langle>f + g\<rangle>\<^sub>C"
        by (metis I.I_length I.pc_interval_axioms One_nat_def Suc_less_eq Suc_pred pc_interval.continuous_segments calculation)
      moreover have "{end\<^sub>C f..<I ! Suc(?i'-1)} \<subseteq> {I ! (?i'-1)..<I ! Suc(?i'-1)}"
        by (auto, metis (no_types, lifting) One_nat_def Suc_pred calculation(2) lessI nth_append nth_mem set_takeWhileD takeWhile_dropWhile_id)
      ultimately have "continuous_on {end\<^sub>C f..<I ! ?i'} \<langle>f + g\<rangle>\<^sub>C"
        by (metis (no_types, lifting) One_nat_def Suc_pred continuous_on_subset)
      with True i show ?thesis
        by (auto simp add: right_pc_interval_def dropWhile_nth) (rule continuous_on_cgf_cat_right[of _ f], auto)
    next
      case False
      with i have i'l: "i + ?i' - Suc 0 < length I - 1"
      proof -
        from False i have "i + ?i' - 1 < length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I @ dropWhile (\<lambda>x. x \<le> end\<^sub>C f) I) - 1"
          by (unfold length_append, auto simp add: right_pc_interval_def)
        thus ?thesis
          by (auto)
      qed
      with False i have "end\<^sub>C f \<le> I ! (i + ?i' - 1)"
        by (rule_tac nth_le_takeWhile_ord, auto)
      moreover have "continuous_on {I ! (i + ?i' - 1)..<I ! Suc (i + ?i' - 1)} \<langle>f + g\<rangle>\<^sub>C"
        by (auto intro: i'l)
      ultimately show ?thesis using i False
        by (auto intro: continuous_on_cgf_cat_right[of _ f] simp add: right_pc_interval_def dropWhile_nth)        
    qed
  qed    
qed

lemma filtermap_within_range_minus: "filtermap (\<lambda> x. x - n::real) (at y within {x..<y}) = (at (y - n) within ({x-n..<y-n}))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])

lemma filtermap_within_range_plus: "filtermap (\<lambda> x. x + n::real) (at y within {x..<y}) = (at (y + n) within ({x+n..<y+n}))"
  using filtermap_within_range_minus[of "-n"] by simp

lemma filter_upto_contract:
  "\<lbrakk> (x::real) \<le> y; y < z \<rbrakk> \<Longrightarrow> (at z within {x..<z}) = (at z within {y..<z})"
  by (rule at_within_nhd[of _ "{y<..<z+1}"], auto)

lemma Lim_cgf_plus_shift: 
  assumes "0 \<le> m" "m < n"
  shows "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (n+end\<^sub>C(f)) within {m+end\<^sub>C(f)..<n+end\<^sub>C(f)})
         \<longleftrightarrow> 
         (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at n within {m..<n})" 
  (is "?L1 \<longleftrightarrow> ?L2")
proof -
  have "?L1 \<longleftrightarrow> ((\<langle>g\<rangle>\<^sub>C \<circ> (\<lambda> x. x - end\<^sub>C(f))) \<longlongrightarrow> L) (at (n+end\<^sub>C(f)) within {m+end\<^sub>C(f)..<n+end\<^sub>C(f)})"
    apply (rule Lim_cong_within, auto)
    using assms(1) cgf_cat_ext_last le_add_same_cancel2 order_trans by (blast intro: Lim_cong_within)
  also have "... = ?L2"
    by (simp add: filtermap_within_range_minus tendsto_compose_filtermap)
  finally show ?thesis .
qed



lemma pc_cvg_interval_left:
  assumes "pc_cvg_interval I (f @\<^sub>C g)"
  shows "pc_cvg_interval (left_pc_interval (end\<^sub>C f) I) f" (is "pc_cvg_interval ?RI f")
proof -
  interpret I: pc_cvg_interval I "(f @\<^sub>C g)" by (simp add: assms) 
  interpret lI: pc_interval "(left_pc_interval (end\<^sub>C f) I)" f
    using I.pc_interval_axioms pc_interval_left by auto
  have "\<And>i. i < length (left_pc_interval (end\<^sub>C f) I) - 1 \<Longrightarrow>
         \<exists>L. (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L)
             (at (left_pc_interval (end\<^sub>C f) I ! Suc i) within {left_pc_interval (end\<^sub>C f) I ! i..<left_pc_interval (end\<^sub>C f) I ! Suc i})"
  proof -
    let ?i' = "length (takeWhile (\<lambda>x. x < end\<^sub>C f) I)"
    fix i
    assume i: "i < length (left_pc_interval (end\<^sub>C f) I) - 1"
    hence ef_nz: "end\<^sub>C f > 0"
      by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, metis I.nth_I_nz le_less_trans length_takeWhile_le not_less nth_mem set_takeWhileD takeWhile_nth)

    show "\<exists>L. (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L)
               (at (left_pc_interval (end\<^sub>C f) I ! Suc i) within {left_pc_interval (end\<^sub>C f) I ! i..<left_pc_interval (end\<^sub>C f) I ! Suc i})"
    proof (cases "Suc i < ?i'")
      case True
      hence "left_pc_interval (end\<^sub>C f) I ! i = I ! i"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
      moreover have "left_pc_interval (end\<^sub>C f) I ! Suc i = I ! Suc i"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth True)
      moreover obtain L where "((\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i}))"
        by (metis I.I_length One_nat_def Suc_less_eq Suc_pred True assms length_takeWhile_le less_le_trans pc_cvg_interval.cvg_segments)
      moreover have "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i}) \<longleftrightarrow> (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i})"
        by (rule Lim_cong_within, auto, metis True cgf_cat_ext_first le_less_trans not_le nth_mem order.asym set_takeWhileD takeWhile_nth)
      ultimately show ?thesis
        by auto
    next
      case False
      have lI: "last I \<ge> end\<^sub>C f"
        by (simp add: I.I_last cgf_sub_end)
      have ltI: "?i' > 0"
          by (metis One_nat_def add.left_neutral cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc i left_pc_interval_def length_append length_greater_0_conv less_nat_zero_code list.size(3) list.size(4))       
      from False i have i_def: "i = ?i' - 1"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
      have "left_pc_interval (end\<^sub>C f) I ! i = I ! i"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, metis Suc_eq_plus1_left add.commute add.right_neutral cancel_ab_semigroup_add_class.add_diff_cancel_left' i left_pc_interval_def length_append list.size(3) list.size(4))
      moreover from False have "left_pc_interval (end\<^sub>C f) I ! Suc i = end\<^sub>C f"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, metis (no_types) Suc_eq_plus1_left Suc_leI add.commute add.left_neutral cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc diff_is_0_eq i left_pc_interval_def length_append list.size(3) list.size(4) nth_Cons')
      moreover have Ii: "I ! i < end\<^sub>C f"
        by (metis Suc_eq_plus1_left add.commute calculation(1) calculation(2) i lI.I_distinct lI.I_sorted sorted_distinct)
      moreover have I_ge_end:"I ! Suc i \<ge> end\<^sub>C f"
      proof -
        from lI have "I ! length (takeWhile (\<lambda>x. x < end\<^sub>C f) I) \<ge> end\<^sub>C f"
          by (rule_tac nth_length_takeWhile_less, auto, metis I.I_z empty_iff last_in_set list.set(1))
        with ltI show ?thesis
          by (simp add: i_def)
      qed
      obtain L where "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
      proof -
        have "I ! Suc i > end\<^sub>C f \<Longrightarrow> \<exists>L. (\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
        proof (rule_tac x="\<langle>g\<rangle>\<^sub>C 0" in exI)
          assume a:"I ! Suc i > end\<^sub>C f"
          have "continuous_on {I ! i..<I ! Suc i} \<langle>f + g\<rangle>\<^sub>C"
            by (rule I.continuous_segments, metis I.I_length Suc_diff_1 Suc_eq_plus1_left add.commute i_def lI last_in_set length_takeWhile_less less_diff_conv list.size(3) ltI nat.simps(3) not_less)
          thus "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> \<langle>g\<rangle>\<^sub>C 0) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
            apply (simp add: continuous_on_def)
            apply (drule_tac x="end\<^sub>C f" in bspec)
            apply (metis Suc_diff_1 a atLeastLessThan_iff calculation(1) i_def left_pc_interval_def lessI ltI not_less nth_append nth_mem order.asym set_takeWhileD)
            apply (simp add: I_ge_end cgf_cat_ext_last tendsto_within_subset)
          done
        qed
        moreover have "\<exists>L. (\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i})"
          by (metis (full_types) I.cvg_segments Ii Suc_le_eq Suc_pred' i_def lI last_conv_nth length_takeWhile_le less_SucE list.size(3) ltI not_le not_less0)

        ultimately show ?thesis using that I_ge_end
          by (fastforce)
      qed
      moreover have "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f}) \<longleftrightarrow> (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
        by (rule Lim_cong_within, auto, simp add: cgf_cat_ext_first)
      ultimately show ?thesis
        by (auto)      
    qed
  qed
  thus ?thesis
    by (unfold_locales, simp)
qed

lemma pc_cvg_interval_right:
  assumes "pc_cvg_interval I (f @\<^sub>C g)"
  shows "pc_cvg_interval (right_pc_interval (end\<^sub>C f) I) g" (is "pc_cvg_interval ?RI g")
proof -
  interpret I: pc_cvg_interval I "(f @\<^sub>C g)" by (simp add: assms) 
  interpret rI: pc_interval "(right_pc_interval (end\<^sub>C f) I)" g
    by (simp add: I.pc_interval_axioms pc_interval_right)
  show ?thesis
  proof
    show "\<And>i. i < length ?RI - 1 \<Longrightarrow>
          \<exists>L. (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?RI ! Suc i) within {?RI ! i..<?RI ! Suc i})"
    proof -
      fix i
      assume i:"i < length ?RI - 1"
      hence egnz: "end\<^sub>C g > 0"
        by (simp add: right_pc_interval_def, metis I.I_le_end I.I_sorted add.right_neutral cgf_end_0_iff cgf_end_ge_0 dropWhile_sorted_le_above less_eq_real_def not_less nth_mem set_dropWhileD)      
      let ?i' = "length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I)"
      show "\<exists>L. (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?RI ! Suc i) within {?RI ! i..<?RI ! Suc i})"
      proof (cases "i = 0")
        case True 
        have "?i' < length I"
          by (metis I.I_last I.I_length add.right_neutral add_left_cancel append_Nil2 egnz cgf_end_cat cgf_prefix_cat cgf_sub_end last_in_set le_less_trans length_0_conv length_append length_takeWhile_le not_less_iff_gr_or_eq set_takeWhileD takeWhile_dropWhile_id)
        moreover have "?i' > 0"
          by (metis I.I_sorted I.I_z Un_iff cgf_end_ge_0 dropWhile_sorted_le_above empty_iff length_greater_0_conv list.set(1) not_less set_append takeWhile_dropWhile_id)
        moreover have "length (dropWhile (\<lambda>x. x \<le> end\<^sub>C f) I) > 0"
          by (metis add.right_neutral calculation(1) length_append length_greater_0_conv less_not_refl2 list.size(3) takeWhile_dropWhile_id)
        moreover have "I ! (?i'-1) \<le> end\<^sub>C f"
          by (auto, metis One_nat_def Suc_pred calculation(2) last_conv_nth last_in_set length_greater_0_conv lessI nth_append set_takeWhileD takeWhile_dropWhile_id)
        moreover have "(?i'-1) < length I - 1"
          using calculation(1) calculation(2) by linarith
        moreover then obtain L where "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc (?i'-1)) within {I ! (?i'-1)..<I ! Suc (?i'-1)})"
          using I.cvg_segments[of "?i'-1"] by (auto)
        moreover have "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc (?i'-1)) within {end\<^sub>C f..<I ! Suc (?i'-1)})"
          using calculation(1) calculation(2) calculation(4) calculation(6) filter_upto_contract nth_length_takeWhile by fastforce
          
        ultimately show ?thesis using True
          apply (auto simp add: right_pc_interval_def dropWhile_nth)
          apply (subst Lim_cgf_plus_shift[of _ _ f g, THEN sym])
          apply (auto)
          apply (meson not_less nth_length_takeWhile)
        done
      next
        case False
        with i have i'l: "i + ?i' - Suc 0 < length I - 1"
        proof -
        from False i have "i + ?i' - 1 < length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I @ dropWhile (\<lambda>x. x \<le> end\<^sub>C f) I) - 1"
          by (unfold length_append, auto simp add: right_pc_interval_def)
        thus ?thesis
          by (auto)
        qed
        with False i have "end\<^sub>C f \<le> I ! (i + ?i' - 1)"
          by (rule_tac nth_le_takeWhile_ord, auto)
        moreover then obtain L where "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc (i + ?i' - 1)) within {I ! (i + ?i' - 1)..<I ! Suc (i + ?i' - 1)})"
          by (metis One_nat_def assms i'l pc_cvg_interval_axioms_def pc_cvg_interval_def)
        ultimately show ?thesis using i False
          apply (auto  simp add: right_pc_interval_def dropWhile_nth)        
          apply (subst Lim_cgf_plus_shift[of _ _ f g, THEN sym])
          apply (auto)
          apply (metis (no_types, lifting) False I.pc_interval_axioms Nat.add_diff_assoc2 Suc_eq_plus1 Suc_leI add_eq_if i'l pc_interval_def sorted_distinct)
        done
      qed
    qed    
  qed
qed

lemma piecewise_continuous_cat_left:
  assumes "piecewise_continuous (f @\<^sub>C g)"
  shows "piecewise_continuous f"
  using assms pc_interval_left by (auto simp add: piecewise_continuous_def)

lemma piecewise_convergent_cat_left:
  assumes "piecewise_convergent (f @\<^sub>C g)"
  shows "piecewise_convergent f"
  using assms pc_cvg_interval_left by (auto simp add: piecewise_convergent_def)

lemma piecewise_continuous_cat_right:
  assumes "piecewise_continuous (f @\<^sub>C g)"
  shows "piecewise_continuous g"
  using assms pc_interval_right by (auto simp add: piecewise_continuous_def)

lemma piecewise_convergent_cat_right:
  assumes "piecewise_convergent (f @\<^sub>C g)"
  shows "piecewise_convergent g"
  using assms pc_cvg_interval_right by (auto simp add: piecewise_convergent_def)

lemma pc_interval_cat:
  assumes "pc_interval I\<^sub>1 f" "pc_interval I\<^sub>2 g"
  shows "pc_interval (I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)) (f @\<^sub>C g)"
proof (cases "g = []\<^sub>C")
  case True thus ?thesis 
    by (simp, metis append_Nil2 assms(1) assms(2) cgf_end_empty last_in_set length_greater_0_conv length_map list.set_sel(2) not_less pc_interval.I_last pc_interval.I_length pc_interval.tl_I_ge_0 pc_interval_def sorted_last)
next
  case False note gne = this
  hence gegz: "end\<^sub>C(g) > 0"
    using cgf_end_0_iff cgf_end_ge_0 less_eq_real_def by auto 

  interpret I\<^sub>1: pc_interval I\<^sub>1 f by (simp add: assms)
  interpret I\<^sub>2: pc_interval I\<^sub>2 g by (simp add: assms)

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

  

  ultimately show "pc_interval ?I (f @\<^sub>C g)"
    by (unfold_locales, simp_all add: cgf_end_cat)
qed
  
lemma piecewise_continuous_cat:
  assumes "piecewise_continuous f" "piecewise_continuous g"
  shows "piecewise_continuous (f @\<^sub>C g)"
  using assms
  by (auto intro: pc_interval_cat simp add: piecewise_continuous_def)
     
lemma piecewise_continuous_cat_iff:
  "piecewise_continuous (f @\<^sub>C g) \<longleftrightarrow> piecewise_continuous f \<and> piecewise_continuous g"
  using piecewise_continuous_cat piecewise_continuous_cat_left piecewise_continuous_cat_right by blast

lemma pc_cvg_interval_cat:
  assumes "pc_cvg_interval I\<^sub>1 f" "pc_cvg_interval I\<^sub>2 g"
  shows "pc_cvg_interval (I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)) (f @\<^sub>C g)"
proof -
  interpret I\<^sub>1: pc_cvg_interval I\<^sub>1 f by (simp add: assms)
  interpret I\<^sub>2: pc_cvg_interval I\<^sub>2 g by (simp add: assms)
  let ?I = "I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)"
  interpret I: pc_interval ?I "(f @\<^sub>C g)"
    using pc_interval_cat[of I\<^sub>1 f I\<^sub>2 g] I\<^sub>1.pc_interval_axioms I\<^sub>2.pc_interval_axioms by blast
  have "\<And> i. i < length(?I) - 1 \<Longrightarrow> \<exists> L. (\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)})"
  proof (simp)
    fix i
    assume i:"i < length I\<^sub>1 + (length I\<^sub>2 - Suc 0) - Suc 0" 

    thus "\<exists> L. (\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)})"
    proof (cases "i < length I\<^sub>1 - 1")
      case True
      then obtain L where "(\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)})" (is "(_ \<longlongrightarrow> _) (?F)")
        by (metis I\<^sub>1.I_length I\<^sub>1.pc_cvg_interval_axioms One_nat_def Suc_diff_Suc Suc_mono cancel_comm_monoid_add_class.diff_zero less_SucI nth_append pc_cvg_interval.cvg_segments)
      moreover have "(\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) ?F \<longleftrightarrow> (\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) ?F"
        by (rule Lim_cong_within, simp_all, metis I\<^sub>1.I_last I\<^sub>1.I_sorted Suc_eq_plus1 True cgf_cat_ext_first in_set_conv_nth less_diff_conv less_le_trans nth_append sorted_last)
      ultimately show ?thesis
        by blast
    next
      case False
      have Ii: "?I ! i = (I\<^sub>2 ! (i - (length I\<^sub>1 - Suc 0))) + end\<^sub>C(f)"
      proof (cases "i < length I\<^sub>1")
        case True
        moreover have "i = length I\<^sub>1 - Suc 0"
          using False calculation by linarith
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
      from i False have ISi: "?I!(Suc i) = (I\<^sub>2 ! Suc (i - (length I\<^sub>1 - Suc 0))) + end\<^sub>C(f)"
        by (auto simp add: nth_append, metis I\<^sub>1.I_length I\<^sub>2.I_length Nitpick.size_list_simp(2) One_nat_def Suc_diff_eq_diff_pred gr_implies_not0 list.exhaust_sel nth_Cons_Suc)

      from ISi Ii obtain L where L:"(\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i) - end\<^sub>C(f)) within {?I!i - end\<^sub>C(f) ..< ?I!(Suc i) - end\<^sub>C(f)})" (is "(_ \<longlongrightarrow> _) (?F1)")
        by (simp, metis False I\<^sub>1.I_length I\<^sub>2.cvg_segments Nat.add_diff_assoc2 One_nat_def Suc_leI add_diff_inverse_nat add_less_cancel_left i)
      
      have "(\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)}) \<longleftrightarrow>
            ((\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<circ> (\<lambda> x. x + end\<^sub>C(f))) \<longlongrightarrow> L) ?F1"
        by (simp add: tendsto_compose_filtermap filtermap_within_range_plus)
      also have "... \<longleftrightarrow> (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) ?F1"
          apply (rule Lim_cong_within)
          apply (auto simp add: Ii ISi)
          apply (smt False i I\<^sub>1.I_length I\<^sub>2.nth_I_nz Nat.add_diff_assoc2 One_nat_def Suc_leI add_diff_inverse_nat add_less_cancel_left cgf_cat_ext_last diff_le_self less_le_trans)
      done
      finally show ?thesis
        using L by blast
    qed
  qed
  thus ?thesis
    by (unfold_locales, auto)
qed   
  

lemma piecewise_convergent_cat:
  assumes "piecewise_convergent f" "piecewise_convergent g"
  shows "piecewise_convergent (f @\<^sub>C g)"
  using assms
  by (auto intro: pc_cvg_interval_cat simp add: piecewise_convergent_def)

lemma piecewise_convergent_cat_iff:
  "piecewise_convergent (f @\<^sub>C g) \<longleftrightarrow> piecewise_convergent f \<and> piecewise_convergent g"
  using piecewise_convergent_cat piecewise_convergent_cat_left piecewise_convergent_cat_right by blast

lemma piecewise_continuous_minus:
  assumes "piecewise_continuous f" "piecewise_continuous g" "f \<le> g"
  shows "piecewise_continuous (g - f)"
proof -
  obtain h where "g = f @\<^sub>C h"
    using assms(3) cgf_prefix_iff by blast
  with assms show ?thesis
    using piecewise_continuous_cat_right by auto
qed

lemma piecewise_convergent_minus:
  assumes "piecewise_convergent f" "piecewise_convergent g" "f \<le> g"
  shows "piecewise_convergent (g - f)"
proof -
  obtain h where "g = f @\<^sub>C h"
    using assms(3) cgf_prefix_iff by blast
  with assms show ?thesis
    using piecewise_convergent_cat_right by auto
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
  "{f :: 'a cgf. piecewise_convergent f}"
  by (rule_tac x="[]\<^sub>C" in exI, simp)

setup_lifting type_definition_ttrace

instantiation ttrace :: (topological_space) zero
begin
  lift_definition zero_ttrace :: "'a ttrace" is 0 by auto
instance ..
end

abbreviation (input) tt_empty :: "'a::topological_space ttrace" ("[]\<^sub>t") where "[]\<^sub>t \<equiv> 0"

instantiation ttrace :: (topological_space) plus
begin

lift_definition plus_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> 'a ttrace"
is "op +" by (simp add: piecewise_convergent_cat)

instance ..

end

abbreviation (input) tt_cat :: "'a::topological_space ttrace \<Rightarrow> 'a ttrace \<Rightarrow> 'a ttrace" (infixl "@\<^sub>t" 85) 
where "xs @\<^sub>t ys \<equiv> xs + ys"

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
  is "op -" using piecewise_convergent_minus by fastforce

  instance ..

end

lemma tt_self_cancel [simp]: "t - t = []\<^sub>t"
  by (transfer, simp)

lemma tt_minus_empty [simp]: "t - []\<^sub>t = t"
  by (transfer, simp)

lemma tt_append_cancel [simp]: "(x @\<^sub>t y) - x = y"
  by (transfer, auto)

instance ttrace :: (topological_space) ordered_cancel_monoid_diff
  apply (intro_classes)
  apply (transfer, simp add: add.assoc)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, simp)
  apply (transfer, metis cgf_prefix_iff mem_Collect_eq piecewise_convergent_cat_right)
done

lift_definition tt_end :: "'a::topological_space ttrace \<Rightarrow> real" ("end\<^sub>t") is "cgf_end" .

lemma tt_end_ge_0 [simp]: "end\<^sub>t(f) \<ge> 0" by (transfer, simp)

lemma tt_end_empty [simp]: "end\<^sub>t([]\<^sub>t) = 0" by (transfer, simp)

lemma tt_end_0_iff: "end\<^sub>t(f) = 0 \<longleftrightarrow> f = []\<^sub>t"
  by (transfer, simp add: cgf_end_0_iff)

lemma tt_end_cat: "end\<^sub>t(f @\<^sub>t g) = end\<^sub>t(f)+end\<^sub>t(g)"
  by (transfer, simp add: cgf_end_cat)

lemma tt_end_minus: "g \<le> f \<Longrightarrow> end\<^sub>t(f-g) = end\<^sub>t(f)-end\<^sub>t(g)"
  by (transfer, simp add: cgf_end_minus)

lift_definition tt_apply :: "'a::topological_space ttrace \<Rightarrow> real \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>t") is cgf_apply .

lemma tt_apply_minus [simp]: "\<lbrakk> 0 \<le> x; f \<le> g \<rbrakk> \<Longrightarrow> \<langle>g - f\<rangle>\<^sub>t x = \<langle>g\<rangle>\<^sub>t (x + end\<^sub>t(f))"
  by (transfer, simp)

lemma tt_cat_ext_first: "x < end\<^sub>t f \<Longrightarrow> \<langle>f @\<^sub>t g\<rangle>\<^sub>t x = \<langle>f\<rangle>\<^sub>t x"
  by (transfer, simp add: cgf_cat_ext_first)

lemma tt_cat_ext_last: "x \<ge> end\<^sub>t f \<Longrightarrow> \<langle>f @\<^sub>t g\<rangle>\<^sub>t x = \<langle>g\<rangle>\<^sub>t (x - end\<^sub>t f)"
  by (transfer, simp add: cgf_cat_ext_last)

lemma tt_prefix_cat: "f \<le> f @\<^sub>t g"
  using ordered_cancel_monoid_diff_class.le_iff_add by blast

lift_definition tt_restrict :: "'a::topological_space ttrace \<Rightarrow> real \<Rightarrow> 'a ttrace" (infix "\<restriction>\<^sub>t" 85)
is "\<lambda> f n. f \<restriction>\<^sub>C n"
proof -
  fix f :: "'a cgf" and n
  assume a: "piecewise_convergent f"
  have "f = (f \<restriction>\<^sub>C n) @\<^sub>C (f - (f \<restriction>\<^sub>C n))"
    by (simp add: cgf_cat_minus_prefix cgf_restrict_le)
  with a show "piecewise_convergent (f \<restriction>\<^sub>C n)"
    by (metis piecewise_convergent_cat_left)
qed

lemma tt_restrict_le: "t \<restriction>\<^sub>t n \<le> t"
  by (transfer, simp add: cgf_restrict_le)

lemma tt_restrict_empty [simp]: "[]\<^sub>t \<restriction>\<^sub>t n = []\<^sub>t"
  by (transfer, simp)

lemma tt_end_restrict [simp]: "\<lbrakk> 0 \<le> n; n \<le> end\<^sub>t f \<rbrakk> \<Longrightarrow> end\<^sub>t (f \<restriction>\<^sub>t n) = n"
  by (transfer, simp)

(* A non-empty timed trace can always be divided into two non-empty sections *)

lemma ttrace_divisible: 
  assumes "end\<^sub>t(t) > 0"
  obtains t\<^sub>1 t\<^sub>2 where "t = t\<^sub>1 + t\<^sub>2" "end\<^sub>t(t\<^sub>1) > 0" "end\<^sub>t(t\<^sub>2) > 0"
proof -
  have "t = t \<restriction>\<^sub>t (end\<^sub>t t / 2) @\<^sub>t (t - t \<restriction>\<^sub>t (end\<^sub>t t / 2))"
    by (metis cancel_monoid_add_class.add_diff_cancel_left' ordered_cancel_monoid_diff_class.le_iff_add tt_restrict_le)
  moreover have "end\<^sub>t(t \<restriction>\<^sub>t (end\<^sub>t t / 2)) > 0"
    by (simp add: assms)
  moreover have "end\<^sub>t(t - t \<restriction>\<^sub>t (end\<^sub>t t / 2)) > 0"
    by (simp add: tt_end_minus tt_restrict_le assms)
  ultimately show ?thesis
    using that by blast
qed

lemma piecewise_convergent_end:
  assumes "piecewise_convergent t" "0 < end\<^sub>C t"
  obtains l where "(\<langle>t\<rangle>\<^sub>C \<longlongrightarrow> l) (at_left (end\<^sub>C t))"
proof -
  obtain I where pcI: "pc_cvg_interval I t"
    using assms(1) pc_cvg_interval_def piecewise_convergent_def by blast
  have I_end: "I!(length I - 1) = end\<^sub>C(t)"
    by (metis last_conv_nth less_numeral_extra(3) list.size(3) pcI pc_cvg_interval_def pc_interval.I_last pc_interval.I_length)
  let ?k = "I!(length I - 2)"
  have k_Suc: "Suc (length I - 2) = length I - 1"
    using assms(2) pcI pc_cvg_interval.axioms(1) pc_interval.ne_f_I_length by fastforce
  have k_end: "?k < end\<^sub>C t"
    by (metis I_end Suc_eq_plus1 k_Suc lessI pcI pc_cvg_interval_def pc_interval_def sorted_distinct)
  obtain L where L:"(\<langle>t\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C t) within {?k..<end\<^sub>C(t)})"
    by (metis I_end k_Suc lessI pcI pc_cvg_interval.axioms(2) pc_cvg_interval_axioms_def)
  from k_end have at_left_end: "(at_left (end\<^sub>C t)) = at (end\<^sub>C t) within {?k..<end\<^sub>C(t)}"
    by (rule_tac at_within_nhd[of _ "{?k<..<end\<^sub>C(t)+1}"], auto)
  from that show ?thesis
    using L at_left_end by auto
qed

lemma ttrace_convergent_end:
  assumes "0 < end\<^sub>t t"
  obtains l where "(\<langle>t\<rangle>\<^sub>t \<longlongrightarrow> l) (at_left (end\<^sub>t t))"
  using assms
  by (transfer, blast intro: piecewise_convergent_end)

text {* Hide implementation details for cgfs and ttraces *}
  
lifting_update cgf.lifting
lifting_forget cgf.lifting

lifting_update ttrace.lifting
lifting_forget ttrace.lifting

end