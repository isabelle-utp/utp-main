section {* Timed traces *}

theory ttrace
  imports Real_Vector_Spaces Map_Extra List_extra
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

subsection {* Contiguous functions *}

typedef 'a cgf = 
  "{f :: real \<rightharpoonup> 'a. (\<exists> i. i \<ge> 0 \<and> dom(f) = {0..<i})}"
  by (rule_tac x="Map.empty" in exI, auto)

setup_lifting type_definition_cgf

lift_definition cgf_apply :: "'a cgf \<Rightarrow> real \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>C") is "\<lambda> f x. the (f x)" .
lift_definition cgf_dom :: "'a cgf \<Rightarrow> real set" ("dom\<^sub>C") is dom .
lift_definition cgf_end :: "'a cgf \<Rightarrow> real" ("end\<^sub>C") is "\<lambda> f. if (dom(f) = {}) then 0 else Sup(dom(f))" .
lift_definition cgf_empty :: "'a cgf" ("[]\<^sub>C") is Map.empty by (auto)
lift_definition cgf_cat :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf" (infixl "@\<^sub>C" 85)
is "\<lambda> f g. if (dom f = {}) then g else (\<lambda> x. if (x < Sup(dom(f))) then f x else g (x - Sup(dom(f))))"
  apply (auto simp add: dom_if)
  apply (rename_tac f g i j)
  apply (subgoal_tac "i > 0")
  apply (simp add: dom_shift_minus plus_image_atLeastLessThan)
  apply (rule_tac x="j + i" in exI)
  apply (auto)
done

lemma cgf_cat_left_unit [simp]: "[]\<^sub>C @\<^sub>C t = t"
  by (transfer, simp)

lemma cgf_cat_right_unit [simp]: "t @\<^sub>C []\<^sub>C = t"
  apply (transfer, auto)
  apply (rename_tac t i)
  apply (subgoal_tac "i > 0")
  apply (simp)
  apply (rule ext)
  apply (fastforce)+
done

lemma map_eqI:
  "\<lbrakk> dom f = dom g; \<forall> x\<in>dom(f). the(f x) = the(g x) \<rbrakk> \<Longrightarrow> f = g"
  by (metis domIff map_le_antisym map_le_def option.expand)

lemma cgf_eqI: "\<lbrakk> end\<^sub>C f = end\<^sub>C g; \<forall> x<end\<^sub>C g. \<langle>f\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C x \<rbrakk> \<Longrightarrow> f = g"
  apply (transfer)
  apply (rename_tac f g)
  apply (case_tac "dom(f) = {}")
  apply (auto)[1]
  apply (case_tac "g = Map.empty")
  apply (simp_all)
  using less_eq_real_def apply auto[1]
  apply (case_tac "g = Map.empty")
  apply (auto)
  using less_eq_real_def apply auto[1]
  apply (rule map_eqI)
  using less_eq_real_def apply auto
done

lemma cgf_end_empty: "end\<^sub>C([]\<^sub>C) = 0"
  by (transfer, simp)

lemma cgf_end_cat: "end\<^sub>C(f @\<^sub>C g) = end\<^sub>C(f)+end\<^sub>C(g)"
  apply (transfer)
  apply (rename_tac f g)
  apply (case_tac "dom(f) = {}")
  apply (simp)
  apply (clarify)
  apply (subgoal_tac "0 < i")
  apply (auto)
oops

lemma cgf_cat_assoc: "(x @\<^sub>C y) @\<^sub>C z = x @\<^sub>C (y @\<^sub>C z)"
  apply (transfer)
  apply (rename_tac x y z)
  apply (case_tac "dom x = {}")
  apply (simp_all)
  apply (clarsimp)
  apply (rename_tac x y z i j k)
  apply (subgoal_tac "i > 0")
  apply (clarsimp)
  apply (safe)
  apply (rule ext)
oops

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

abbreviation cgf_prefix :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> bool" (infix "\<subseteq>\<^sub>C" 50)
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
"\<lambda> f g. if (g \<subseteq>\<^sub>m f \<and> dom g \<noteq> {}) then (\<lambda> x. if (x \<ge> 0 \<and> x < (Sup(dom f) - Sup(dom g))) then f (x + Sup(dom g)) else None) else f"
  apply (auto simp add: dom_shift_plus dom_if)
  apply (rename_tac f g i j)
  apply (subgoal_tac "0 < i")
  apply (subgoal_tac "0 < j")
  apply (simp)
  apply (rule_tac x="i - j" in exI)
  apply (subgoal_tac "0 < j")
  apply (auto)
  using map_le_implies_dom_le apply fastforce
  apply (metis add.commute add_less_cancel_left diff_add_cancel le_diff_eq less_eq_real_def less_iff_diff_less_0 less_trans not_less order_refl order_trans)
  using map_le_implies_dom_le apply fastforce
done 

instance ..
end

lemma cgf_minus_self [simp]: "f - f = []\<^sub>C"
  by (transfer, rule ext, auto)

lemma cgf_cat_minus [simp]: "f @\<^sub>C g - f = g"
  apply (transfer)
  apply (rename_tac f g)
  apply (case_tac "dom f = {}")
  apply (auto simp add: map_le_def dom_if)
  apply (rename_tac f g i j)
  apply (rule ext)
  apply (auto)
  apply fastforce
  apply (subgoal_tac "0 < i")
  apply (simp add: dom_shift_minus plus_image_atLeastLessThan)
  apply (subgoal_tac "{0..<i} \<inter> {x. x < i} \<union> {i..<j + i} \<inter> {x. \<not> x < i} = {0..<j+i}")
  apply (simp)
  apply (metis atLeastLessThan_iff domIff)
  apply (auto)
  apply (rule ext)
  apply (auto)
  using less_eq_real_def apply auto
done

lemma cgf_cat_minus_prefix:
  "f \<le> g \<Longrightarrow> g = f @\<^sub>C (g - f)"
  apply (transfer, auto)
  apply (rule ext)
  apply (auto)
  apply (metis atLeastLessThan_empty_iff2 atLeastLessThan_iff cSup_atLeastLessThan domIff dom_eq_empty_conv map_le_def)
  apply (metis atLeastLessThan_empty cSup_atLeastLessThan domIff empty_iff ivl_subset less_eq_real_def less_le_trans map_le_implies_dom_le)
  using less_eq_real_def apply auto
done

lemma cgf_prefix_iff: "f \<le> g \<longleftrightarrow> (\<exists> h. g = f @\<^sub>C h)"
  apply (auto)
  apply (rule_tac x="g - f" in exI)
  apply (simp add: cgf_cat_minus_prefix)
done

definition piecewise_continuous :: "'a::topological_space cgf \<Rightarrow> bool" where
"piecewise_continuous f = (end\<^sub>C(f) = 0 \<or>
  (\<exists> I. set(I) \<subseteq> {0 .. end\<^sub>C f} \<and> {0, end\<^sub>C f} \<subseteq> set(I) \<and> sorted I \<and> distinct I \<and> 
        (\<forall> i < length(I) - 1. continuous_on {I!i ..< I!(Suc i)} \<langle>f\<rangle>\<^sub>C)))"

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

lemma 
  assumes "piecewise_continuous g" "f \<subseteq>\<^sub>C g"
  shows "piecewise_continuous f"
proof (cases "end\<^sub>C f = 0")
  case True thus ?thesis
    by (simp add: piecewise_continuous_def)
next
  case False 
  note ef = this with assms show ?thesis
  proof (cases "end\<^sub>C g = 0")
    case True with assms show ?thesis
      by (auto simp add: piecewise_continuous_def, metis (full_types) cgf_end_empty cgf_prefix_least cgf_sub_end dual_order.antisym)
  next
    case False with ef assms show ?thesis
    proof (clarsimp simp add: piecewise_continuous_def)

    fix I
    assume I:"ran\<^sub>l I \<subseteq> {0..end\<^sub>C g}" "0 \<in> ran\<^sub>l I" "end\<^sub>C g \<in> ran\<^sub>l I" "sorted I" "distinct I"
             "\<forall>i<length I - Suc 0. continuous_on {I ! i..<I ! Suc i} \<langle>g\<rangle>\<^sub>C"

    obtain I\<^sub>1 I\<^sub>2 where I_split: "I = I\<^sub>1 @ I\<^sub>2" "set(I\<^sub>1) \<subseteq> {0..end\<^sub>C f}" "set(I\<^sub>2) \<subseteq> {end\<^sub>C f<..end\<^sub>C g}"
    proof -
      have "I = takeWhile (\<lambda> x. x \<le> end\<^sub>C f) I @ dropWhile (\<lambda> x. x \<le> end\<^sub>C f) I"
        by simp
      moreover have "set(takeWhile (\<lambda> x. x \<le> end\<^sub>C f) I) \<subseteq> {0..end\<^sub>C f}"
        by (auto, meson I(1) atLeastAtMost_iff set_takeWhileD subsetCE, meson set_takeWhileD)
      moreover have "set(dropWhile (\<lambda> x. x \<le> end\<^sub>C f) I) \<subseteq> {end\<^sub>C f<..end\<^sub>C g}"
        by (auto intro!: I(4) dropWhile_sorted_le_above[of I], meson I(1) atLeastAtMost_iff set_dropWhileD subsetCE) 
      ultimately show ?thesis using that by blast
    qed

    have I\<^sub>1_zero: "0 \<in> set I\<^sub>1"
    proof -
      from I I_split have "0 \<in> set(I\<^sub>1 @ I\<^sub>2)"
        by (simp)
      with I_split(3) show ?thesis
        by (auto, metis Set.set_insert cgf_end_empty cgf_prefix_least cgf_sub_end greaterThanAtMost_iff insert_subset not_less)
    qed

    have I\<^sub>1_sd: "sorted I\<^sub>1" "distinct I\<^sub>1"
      using I(4,5) I_split(1) sorted_append distinct_append by blast+

    show "\<exists>I. ran\<^sub>l I \<subseteq> {0..end\<^sub>C f} \<and> 
              0 \<in> ran\<^sub>l I \<and> 
              end\<^sub>C f \<in> ran\<^sub>l I \<and> 
              sorted I \<and> distinct I \<and> 
              (\<forall>i<length I - Suc 0. continuous_on {I ! i..<I ! Suc i} \<langle>f\<rangle>\<^sub>C)"
    proof (cases "end\<^sub>C f \<in> set(I\<^sub>1)")
      case True note ef = this
      have last_I\<^sub>1: "last(I\<^sub>1) = end\<^sub>C f"
      proof (rule ccontr)
        assume "last(I\<^sub>1) \<noteq> end\<^sub>C f"
        hence "last(I\<^sub>1) > end\<^sub>C f"
          by (simp add: I\<^sub>1_sd(1) ef order.not_eq_order_implies_strict)
        moreover have "last(I\<^sub>1) \<in> set(I\<^sub>1)"
          using ef length_pos_if_in_set by force
        ultimately show False
          using I_split(2) by auto
      qed
      from ef show ?thesis
      proof (rule_tac x="I\<^sub>1" in exI, clarsimp simp add: assms I_split I\<^sub>1_zero I\<^sub>1_sd)
        fix i
        assume i: "i < length I\<^sub>1 - Suc 0"
        have "0 \<le> I\<^sub>1 ! i"
          by (meson I_split(2) i atLeastAtMost_iff diff_le_self less_le_trans nth_mem subsetCE)
        moreover have "I\<^sub>1 ! i < I\<^sub>1 ! Suc i"
          by (metis I\<^sub>1_sd(1) I\<^sub>1_sd(2) One_nat_def add.right_neutral add_Suc_right i sorted_distinct)
        moreover have "I\<^sub>1 ! Suc i \<le> end\<^sub>C f"
          by (metis I\<^sub>1_sd(1) Suc_mono Suc_pred ef i last_I\<^sub>1 length_pos_if_in_set nth_mem sorted_last)
        moreover have "continuous_on {I\<^sub>1 ! i..<I\<^sub>1 ! Suc i} \<langle>g\<rangle>\<^sub>C"
        proof -
          have "I\<^sub>1 ! i = I ! i"
            by (metis I_split(1) diff_le_self i less_le_trans nth_append)
          moreover have "I\<^sub>1 ! Suc i = I ! Suc i"
            by (metis I_split(1) Suc_mono Suc_pred ef i length_pos_if_in_set nth_append)
          ultimately show ?thesis
            using I(6) I_split(1) i by auto
        qed

        ultimately show "continuous_on {I\<^sub>1 ! i..<I\<^sub>1 ! Suc i} \<langle>f\<rangle>\<^sub>C"
          by (rule_tac continuous_on_cgf_prefix[of _ g], simp_all add: assms)
     qed
   next        
     case True note ef = this

oops
  
typedef (overloaded) 'a::topological_space ttrace = 
  "{f :: 'a cgf. piecewise_continuous f}"
  by (rule_tac x="cgf_empty" in exI, simp add: piecewise_continuous_def, transfer, auto)

setup_lifting type_definition_ttrace

lift_definition tt_empty :: "'a::topological_space ttrace" ("[]\<^sub>t") is cgf_empty
  by (simp add: piecewise_continuous_def, transfer, auto)

instantiation ttrace :: (topological_space) order
begin

lift_definition less_eq_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> bool" is "op \<le>" .
lift_definition less_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> bool" is "op <" .

instance by (intro_classes, (transfer, simp add: less_cgf_def)+)

end

lemma ttrace_min: "[]\<^sub>t \<le> t"
  by (transfer, simp)

end