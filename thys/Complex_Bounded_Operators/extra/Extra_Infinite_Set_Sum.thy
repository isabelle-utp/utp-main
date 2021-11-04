theory Extra_Infinite_Set_Sum
  imports "HOL-Analysis.Infinite_Set_Sum"
    Jordan_Normal_Form.Conjugate
    \<comment> \<open>\<^theory>\<open>Jordan_Normal_Form.Conjugate\<close> contains the instantiation \<open>complex :: ord\<close>.
               If we define our own instantiation, it would be impossible to load both
               \<^session>\<open>Jordan_Normal_Form\<close> and this theory.\<close>

    Extra_General
begin


subsection\<open>Infinite Set Sum Missing\<close>

definition infsetsum'_converges :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "infsetsum'_converges f A = (\<exists>x. (sum f \<longlongrightarrow> x) (finite_subsets_at_top A))"

definition infsetsum' :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infsetsum' f A = (if infsetsum'_converges f A then Lim (finite_subsets_at_top A) (sum f) else 0)"


lemma infsetsum'_converges_cong: 
  assumes t1: "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsetsum'_converges f A = infsetsum'_converges g A"
proof-
  have "sum f X = sum g X"
    if "finite X" and "X \<subseteq> A"
    for X
    by (meson Finite_Cartesian_Product.sum_cong_aux subsetD t1 that(2))    
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum g x"
    by (simp add: eventually_finite_subsets_at_top_weakI)
  hence  "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A) =
         (sum g \<longlongrightarrow> x) (finite_subsets_at_top A)"
    for x
    by (simp add: filterlim_cong)
  thus ?thesis
    by (simp add: infsetsum'_converges_def)
qed

lemma infsetsum'_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsetsum' f A = infsetsum' g A"
proof-
  have "sum f X = sum g X"
    if "finite X" and "X \<subseteq> A"
    for X
    by (meson Finite_Cartesian_Product.sum_cong_aux assms in_mono that(2))    
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum g x"
    by (rule eventually_finite_subsets_at_top_weakI)
  hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A) \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top A)" 
    for x
    by (rule tendsto_cong)
  hence "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top A) (sum g)"
    unfolding Topological_Spaces.Lim_def[abs_def]
    by auto
  thus ?thesis
    unfolding infsetsum'_def
    using assms infsetsum'_converges_cong by auto
qed

lemma abs_summable_finiteI0:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
    and "B \<ge> 0"
  shows "f abs_summable_on S" and "infsetsum (\<lambda>x. norm (f x)) S \<le> B"
proof-
  have t1: "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B"
  proof(cases "S = {}")
    case True
    thus ?thesis
      by (simp add: assms(2)) 
  next
    case False
    define M normf where "M = count_space S" and "normf x = ennreal (norm (f x))" for x
    have "sum normf F \<le> ennreal B"
      if "finite F" and "F \<subseteq> S" and
        "\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> (\<Sum>i\<in>F. ennreal (norm (f i))) \<le> ennreal B" and
        "ennreal 0 \<le> ennreal B"
      for F
      using that unfolding normf_def[symmetric] by simp    
    hence normf_B: "finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum normf F \<le> ennreal B" for F
      using assms[THEN ennreal_leI] 
      by auto
    have "integral\<^sup>S M g \<le> B" if "simple_function M g" and "g \<le> normf" for g 
    proof -
      define gS where "gS = g ` S"
      have "finite gS"
        using that unfolding gS_def M_def simple_function_count_space by simp
      have "gS \<noteq> {}" unfolding gS_def False
        by (simp add: False) 
      define part where "part r = g -` {r} \<inter> S" for r
      have r_finite: "r < \<infinity>" if "r : gS" for r 
        using \<open>g \<le> normf\<close> that unfolding gS_def le_fun_def normf_def apply auto
        using ennreal_less_top neq_top_trans top.not_eq_extremum by blast
      define B' where "B' r = (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)" for r
      have B'fin: "B' r < \<infinity>" for r
      proof -
        have "B' r \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)"
          unfolding B'_def
          by (metis (mono_tags, lifting) SUP_least SUP_upper)
        also have "\<dots> \<le> B"
          using normf_B unfolding part_def
          by (metis (no_types, lifting) Int_subset_iff SUP_least mem_Collect_eq)
        also have "\<dots> < \<infinity>"
          by simp
        finally show ?thesis by simp
      qed
      have sumB': "sum B' gS \<le> ennreal B + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        define N \<epsilon>N where "N = card gS" and "\<epsilon>N = \<epsilon> / N"
        have "N > 0" 
          unfolding N_def using \<open>gS\<noteq>{}\<close> \<open>finite gS\<close>
          by (simp add: card_gt_0_iff)
        from \<epsilon>N_def that have "\<epsilon>N > 0"
          by (simp add: ennreal_of_nat_eq_real_of_nat ennreal_zero_less_divide)
        have c1: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and>
             finite y \<and> y \<subseteq> part r"
          if "B' r = 0"
          for r
          using that by auto
        have c2: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and>
             finite y \<and> y \<subseteq> part r"
          if "B' r \<noteq> 0"
          for r
        proof-
          have "B' r - \<epsilon>N < B' r"
            using B'fin \<open>0 < \<epsilon>N\<close> ennreal_between that by fastforce
          have "B' r - \<epsilon>N < Sup (sum normf ` {F. finite F \<and> F \<subseteq> part r}) \<Longrightarrow>
               \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and> finite F \<and> F \<subseteq> part r"
            by (metis (no_types, lifting) leD le_cases less_SUP_iff mem_Collect_eq)
          hence "B' r - \<epsilon>N < B' r \<Longrightarrow>
                \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and>
                finite F \<and> F \<subseteq> part r"
            by (subst (asm) (2) B'_def)
          then obtain F where "B' r - \<epsilon>N \<le> sum normf F" and "finite F" and "F \<subseteq> part r"
            using \<open>B' r - \<epsilon>N < B' r\<close> by auto  
          thus "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r"
            by (metis add.commute ennreal_minus_le_iff)
        qed
        have "\<forall>x. \<exists>y. B' x \<le> sum normf y + \<epsilon>N \<and>
            finite y \<and> y \<subseteq> part x"
          using c1 c2
          by blast 
        hence "\<exists>F. \<forall>x. B' x \<le> sum normf (F x) + \<epsilon>N \<and> finite (F x) \<and> F x \<subseteq> part x"
          by metis 
        then obtain F where F: "sum normf (F r) + \<epsilon>N \<ge> B' r" and Ffin: "finite (F r)" and Fpartr: "F r \<subseteq> part r" for r
          using atomize_elim by auto
        have w1: "finite gS"
          by (simp add: \<open>finite gS\<close>)          
        have w2: "\<forall>i\<in>gS. finite (F i)"
          by (simp add: Ffin)          
        have False
          if "\<And>r. F r \<subseteq> g -` {r} \<and> F r \<subseteq> S"
            and "i \<in> gS" and "j \<in> gS" and "i \<noteq> j" and "x \<in> F i" and "x \<in> F j"
          for i j x
          by (metis subsetD that(1) that(4) that(5) that(6) vimage_singleton_eq)          
        hence w3: "\<forall>i\<in>gS. \<forall>j\<in>gS. i \<noteq> j \<longrightarrow> F i \<inter> F j = {}"
          using Fpartr[unfolded part_def] by auto          
        have w4: "sum normf (\<Union> (F ` gS)) + \<epsilon> = sum normf (\<Union> (F ` gS)) + \<epsilon>"
          by simp
        have "sum B' gS \<le> (\<Sum>r\<in>gS. sum normf (F r) + \<epsilon>N)"
          using F by (simp add: sum_mono)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (\<Sum>r\<in>gS. \<epsilon>N)"
          by (simp add: sum.distrib)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (card gS * \<epsilon>N)"
          by auto
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + \<epsilon>"
          unfolding \<epsilon>N_def N_def[symmetric] using \<open>N>0\<close> 
          by (simp add: ennreal_times_divide mult.commute mult_divide_eq_ennreal)
        also have "\<dots> = sum normf (\<Union> (F ` gS)) + \<epsilon>" 
          using w1 w2 w3 w4
          by (subst sum.UNION_disjoint[symmetric])
        also have "\<dots> \<le> B + \<epsilon>"
          using \<open>finite gS\<close> normf_B add_right_mono Ffin Fpartr unfolding part_def
          by (simp add: \<open>gS \<noteq> {}\<close> cSUP_least)          
        finally show ?thesis
          by auto
      qed
      hence sumB': "sum B' gS \<le> B"
        using ennreal_le_epsilon ennreal_less_zero_iff by blast
      have "\<forall>r. \<exists>y. r \<in> gS \<longrightarrow> B' r = ennreal y"
        using B'fin less_top_ennreal by auto
      hence "\<exists>B''. \<forall>r. r \<in> gS \<longrightarrow> B' r = ennreal (B'' r)"
        by (rule_tac choice) 
      then obtain B'' where B'': "B' r = ennreal (B'' r)" if "r \<in> gS" for r
        by atomize_elim 
      have cases[case_names zero finite infinite]: "P" if "r=0 \<Longrightarrow> P" and "finite (part r) \<Longrightarrow> P"
        and "infinite (part r) \<Longrightarrow> r\<noteq>0 \<Longrightarrow> P" for P r
        using that by metis
      have emeasure_B': "r * emeasure M (part r) \<le> B' r" if "r : gS" for r
      proof (cases rule:cases[of r])
        case zero
        thus ?thesis by simp
      next
        case finite
        have s1: "sum g F \<le> sum normf F"
          if "F \<in> {F. finite F \<and> F \<subseteq> part r}"
          for F
          using \<open>g \<le> normf\<close> 
          by (simp add: le_fun_def sum_mono)

        have "r * of_nat (card (part r)) = r * (\<Sum>x\<in>part r. 1)" by simp
        also have "\<dots> = (\<Sum>x\<in>part r. r)"
          using mult.commute by auto
        also have "\<dots> = (\<Sum>x\<in>part r. g x)"
          unfolding part_def by auto
        also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum g F)"
          using finite
          by (simp add: Sup_upper)
        also have "\<dots> \<le> B' r"        
          unfolding B'_def
          using s1 SUP_subset_mono by blast
        finally have "r * of_nat (card (part r)) \<le> B' r" by assumption
        thus ?thesis
          unfolding M_def
          using part_def finite by auto
      next
        case infinite
        from r_finite[OF \<open>r : gS\<close>] obtain r' where r': "r = ennreal r'"
          using ennreal_cases by auto
        with infinite have "r' > 0"
          using ennreal_less_zero_iff not_gr_zero by blast
        obtain N::nat where N:"N > B / r'" and "real N > 0" apply atomize_elim
          using reals_Archimedean2
          by (metis less_trans linorder_neqE_linordered_idom)
        obtain F where "finite F" and "card F = N" and "F \<subseteq> part r"
          using infinite(1) infinite_arbitrarily_large by blast
        from \<open>F \<subseteq> part r\<close> have "F \<subseteq> S" unfolding part_def by simp
        have "B < r * N"
          unfolding r' ennreal_of_nat_eq_real_of_nat
          using N \<open>0 < r'\<close> assms(2) r'
          by (metis enn2real_ennreal enn2real_less_iff ennreal_less_top ennreal_mult' less_le mult_less_cancel_left_pos nonzero_mult_div_cancel_left times_divide_eq_right)
        also have "r * N = (\<Sum>x\<in>F. r)"
          using \<open>card F = N\<close> by (simp add: mult.commute)
        also have "(\<Sum>x\<in>F. r) = (\<Sum>x\<in>F. g x)"
          using \<open>F \<subseteq> part r\<close>  part_def sum.cong subsetD by fastforce
        also have "(\<Sum>x\<in>F. g x) \<le> (\<Sum>x\<in>F. ennreal (norm (f x)))"
          by (metis (mono_tags, lifting) \<open>g \<le> normf\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> le_fun_def 
              sum_mono)
        also have "(\<Sum>x\<in>F. ennreal (norm (f x))) \<le> B"
          using \<open>F \<subseteq> S\<close> \<open>finite F\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> normf_B by blast 
        finally have "B < B" by auto
        thus ?thesis by simp
      qed

      have "integral\<^sup>S M g = (\<Sum>r \<in> gS. r * emeasure M (part r))"
        unfolding simple_integral_def gS_def M_def part_def by simp
      also have "\<dots> \<le> (\<Sum>r \<in> gS. B' r)"
        by (simp add: emeasure_B' sum_mono)
      also have "\<dots> \<le> B"
        using sumB' by blast
      finally show ?thesis by assumption
    qed
    hence int_leq_B: "integral\<^sup>N M normf \<le> B"
      unfolding nn_integral_def by (metis (no_types, lifting) SUP_least mem_Collect_eq)
    hence "integral\<^sup>N M normf < \<infinity>"
      using le_less_trans by fastforce
    hence "integrable M f"
      unfolding M_def normf_def by (rule integrableI_bounded[rotated], simp)
    hence v1: "f abs_summable_on S"
      unfolding abs_summable_on_def M_def by simp  

    have "(\<lambda>x. norm (f x)) abs_summable_on S"
      using v1 Infinite_Set_Sum.abs_summable_on_norm_iff[where A = S and f = f]
      by auto
    moreover have "0 \<le> norm (f x)"
      if "x \<in> S" for x
      by simp    
    moreover have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>count_space S) \<le> ennreal B"
      using M_def \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> int_leq_B by auto    
    ultimately have "ennreal (\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> ennreal B"
      by (simp add: nn_integral_conv_infsetsum)    
    hence v2: "(\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> B"
      by (subst ennreal_le_iff[symmetric], simp add: assms)
    show ?thesis
      using v1 v2 by auto
  qed
  show "f abs_summable_on S"
    using t1 by blast
  show "(\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> B"
    using t1 by blast
qed

lemma abs_summable_finiteI:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
  shows "f abs_summable_on S"
proof -
  from assms have "sum (\<lambda>x. norm (f x)) {} \<le> B" by blast
  hence "0 \<le> B" by simp
  thus ?thesis 
    using assms by (rule abs_summable_finiteI0[rotated])
qed

lemma infsetsum_finite_sets:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
    and "B \<ge> 0" and "\<And>x. f x \<ge> 0"
  shows "infsetsum f S \<le> B"
  using abs_summable_finiteI0(2)[where f=f and S=S, OF assms(1-2), simplified]
    assms(3) by auto

lemma abs_summable_finiteI_converse:
  assumes f_sum_S: "f abs_summable_on S"
    and finite_F: "finite F" and FS: "F\<subseteq>S"
  defines "B \<equiv> (infsetsum (\<lambda>x. norm (f x)) S)"
  shows "sum (\<lambda>x. norm (f x)) F \<le> B"
proof-
  have a1: "(\<lambda>x. norm (f x)) abs_summable_on F"
    by (simp add: finite_F)    
  have a2: "(\<lambda>x. norm (f x)) abs_summable_on S"
    by (simp add: f_sum_S)    
  have a3: "x \<in> F \<Longrightarrow> norm (f x) \<le> norm (f x)"
    for x
    by simp
  have a4: "F \<subseteq> S"
    by (simp add: FS)    
  have a5: "x \<in> S - F \<Longrightarrow> 0 \<le> norm (f x)"
    for x
    by simp   
  have "sum (\<lambda>x. norm (f x)) F = infsetsum (\<lambda>x. norm (f x)) F"
    by (simp add: finite_F)    
  also have "infsetsum (\<lambda>x. norm (f x)) F \<le> B"
    unfolding B_def 
    using a1 a2 a3 a4 a5 
    by (simp add: infsetsum_mono_neutral_left)
  finally show ?thesis by assumption
qed

lemma abs_summable_countable:
  fixes \<mu> :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes "\<mu> abs_summable_on T"
  shows "countable {x\<in>T. 0 \<noteq> \<mu> x}"
proof-
  define B where "B = infsetsum (\<lambda>x. norm (\<mu> x)) T"
  have \<mu>sum: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" if "finite F" and "F \<subseteq> T" for F
    unfolding B_def 
    using assms that abs_summable_finiteI_converse by auto
  define S where "S i = {x\<in>T. 1/real (Suc i) < norm (\<mu> x)}" for i::nat
  have "\<exists>i. x \<in> S i" if "0 < norm (\<mu> x)" and "x \<in> T" for x
    using that unfolding S_def
    by (metis (full_types, lifting) mem_Collect_eq nat_approx_posE)     
  hence union: "{x\<in>T. 0 < norm (\<mu> x)} = (\<Union>i. S i)"
    unfolding S_def by auto
  have finiteS: "finite (S i)" for i
  proof (rule ccontr)
    assume "infinite (S i)"
    then obtain F where F_Si: "F \<subseteq> S i" and cardF: "card F > (Suc i)*B" and finiteF: "finite F"
      by (metis One_nat_def ex_less_of_nat_mult infinite_arbitrarily_large lessI mult.commute mult.left_neutral of_nat_0_less_iff of_nat_1)
    from F_Si have F_T: "F \<subseteq> T" 
      unfolding S_def by blast
    from finiteF \<mu>sum F_T have sumF: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" by simp
    have "1 / real (Suc i) \<le> norm (\<mu> x)"
      if "x \<in> F"
      for x
      using that F_Si S_def by auto
    hence "sum (\<lambda>x. norm (\<mu> x)) F \<ge> sum (\<lambda>_. 1/real (Suc i)) F" (is "_ \<ge> \<dots>")
      using sum_mono
      by metis       
    moreover have "\<dots> = real (card F) / (Suc i)"
      by (subst sum_constant_scale, auto)
    moreover have "\<dots> > B"
      using cardF
      by (simp add: linordered_field_class.mult_imp_less_div_pos algebra_simps)
    ultimately have "sum (\<lambda>x. norm (\<mu> x)) F > B"
      by linarith 
    with sumF show False by simp
  qed

  have "countable (S i)"
    if "i \<in> UNIV"
    for i
    using finiteS by (simp add: countable_finite)
  hence "countable (\<Union>i. S i)"
    using countable_UN by simp
  hence "countable {x\<in>T. 0 < norm (\<mu> x)}"
    unfolding union by simp
  thus ?thesis
    by simp
qed


lemma infsetsum_cnj[simp]: "infsetsum (\<lambda>x. cnj (f x)) M = cnj (infsetsum f M)"
  unfolding infsetsum_def by (rule integral_cnj)

lemma infsetsum_Re: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Re (f x)) M = Re (infsetsum f M)"
  unfolding infsetsum_def 
  using integral_Re assms by (simp add: abs_summable_on_def)

lemma infsetsum_Im: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Im (f x)) M = Im (infsetsum f M)"
  unfolding infsetsum_def using assms by (simp add: abs_summable_on_def)

lemma infsetsum_mono_complex:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "f abs_summable_on A" and g_sum: "g abs_summable_on A"
  assumes x: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsetsum f A \<le> infsetsum g A"
proof -
  have a1: "infsetsum f A = Complex (Re (infsetsum f A)) (Im (infsetsum f A))" by auto
  also have a2: "Re (infsetsum f A) = infsetsum (\<lambda>x. Re (f x)) A"
    unfolding infsetsum_def 
    using assms by (simp add: abs_summable_on_def)
  also have a3: "Im (infsetsum f A) = infsetsum (\<lambda>x. Im (f x)) A"
    using f_sum by (rule infsetsum_Im[symmetric])
  finally have fsplit: "infsetsum f A = Complex (\<Sum>\<^sub>ax\<in>A. Re (f x)) (\<Sum>\<^sub>ax\<in>A. Im (f x))" by assumption
  have "infsetsum g A = Complex (Re (infsetsum g A)) (Im (infsetsum g A))" by auto
  also have b2: "Re (infsetsum g A) = infsetsum (\<lambda>x. Re (g x)) A"
    using g_sum by (rule infsetsum_Re[symmetric])
  also have b1: "Im (infsetsum g A) = infsetsum (\<lambda>x. Im (g x)) A "
    using g_sum by (rule infsetsum_Im[symmetric])
  finally have gsplit: "infsetsum g A = Complex (\<Sum>\<^sub>ax\<in>A. Re (g x)) (\<Sum>\<^sub>ax\<in>A. Im (g x))" 
    by assumption
  have Re_leq: "Re (f x) \<le> Re (g x)" if "x\<in>A" for x
    using that assms unfolding less_eq_complex_def by simp
  have Im_eq: "Im (f x) = Im (g x)" if "x\<in>A" for x
    using that assms 
    unfolding less_eq_complex_def by simp
  have Refsum: "(\<lambda>x. Re (f x)) abs_summable_on A"
    using assms(1) abs_Re_le_cmod by (simp add: abs_summable_on_comparison_test[where g=f])
  have Regsum: "(\<lambda>x. Re (g x)) abs_summable_on A"
    using assms(2) abs_Re_le_cmod 
    by (simp add: abs_summable_on_comparison_test[where g=g])
  show "infsetsum f A \<le> infsetsum g A"
    unfolding fsplit gsplit
    by (smt (verit, ccfv_SIG) Im_eq Re_leq Refsum Regsum a2 a3 b1 b2 fsplit gsplit infsetsum_cong infsetsum_mono less_eq_complex_def)
qed

lemma infsetsum_subset_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on B" and "A \<subseteq> B" and "\<And>x. x\<notin>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A \<le> infsetsum f B"
proof -
  have fBA: "f abs_summable_on B - A"
    by (meson Diff_subset abs_summable_on_subset assms(1))
  have "0 = infsetsum (\<lambda>_.0) (B-A)" by auto
  also have "... \<le> infsetsum f (B - A)"
    using assms fBA infsetsum_mono_complex
    by (metis DiffD2 abs_summable_on_0)
  also have "... = infsetsum f B - infsetsum f A"
    using assms by (simp add: infsetsum_Diff)
  finally show ?thesis by auto
qed

lemma infsetsum_subset_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f abs_summable_on B" and "A \<subseteq> B" and "\<And>x. x\<notin>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A \<le> infsetsum f B"
proof -
  have fBA: "f abs_summable_on B - A"
    by (meson Diff_subset abs_summable_on_subset assms(1))
  have "0 = infsetsum (\<lambda>_.0) (B-A)" by auto
  also have "... \<le> infsetsum f (B - A)"
    using assms fBA 
    by (metis DiffD2 calculation infsetsum_nonneg) 
  also have "... = infsetsum f B - infsetsum f A"
    using assms by (simp add: infsetsum_Diff)
  finally show ?thesis by auto
qed

lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "(\<lambda>i. (x i) * (x i)) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i) * (y i)) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule abs_summable_finiteI)
  have aux: "a\<le>a' \<Longrightarrow> b\<le>b' \<Longrightarrow> a+b \<le> a'+b'" for a b a' b' :: real by simp
  fix F assume r1: "finite F" and b4: "F \<subseteq> A"
  define B :: real where "B = (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))"

  have a1: "(\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i))"
  proof (rule infsetsum_mono_neutral_left)
    show "(\<lambda>i. norm (x i * x i)) abs_summable_on F"
      by (simp add: r1)      
    show "(\<lambda>i. norm (x i * x i)) abs_summable_on A"
      by (simp add: x2_sum)      
    show "norm (x i * x i) \<le> norm (x i * x i)"
      if "i \<in> F"
      for i :: 'a
      by simp
    show "F \<subseteq> A"
      by (simp add: b4)     
    show "0 \<le> norm (x i * x i)"
      if "i \<in> A - F"
      for i :: 'a
      by simp 
  qed
  have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
    unfolding norm_mult
    by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
  hence "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm (x i * x i) + norm (y i * y i))"
    by (simp add: sum_mono)
  also have "\<dots> = (\<Sum>i\<in>F. norm (x i * x i)) + (\<Sum>i\<in>F. norm (y i * y i))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>F. norm (y i * y i))"
    by (simp add: \<open>finite F\<close>)
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))" 
    using aux a1
    by (simp add: aux \<open>F \<subseteq> A\<close> \<open>finite F\<close> abs_summable_finiteI_converse x2_sum y2_sum)
  also have "\<dots> = B"
    unfolding B_def by simp
  finally show "(\<Sum>i\<in>F. norm (x i * y i)) \<le> B" by assumption
qed

lemma abs_summable_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
proof
  show "f abs_summable_on A"
    if "(\<lambda>i. cnj (f i)) abs_summable_on A"
    using that abs_summable_on_norm_iff[symmetric]
      abs_summable_on_comparison_test by fastforce    
  show "(\<lambda>i. cnj (f i)) abs_summable_on A"
    if "f abs_summable_on A"
    using that abs_summable_on_norm_iff[symmetric]
      abs_summable_on_comparison_test by fastforce 
qed

lemma ennreal_Sup:
  assumes "bdd_above A" and nonempty: "A\<noteq>{}"
  shows "ennreal (Sup A) = Sup (ennreal ` A)"
proof (rule Sup_eqI[symmetric])
  fix y assume "y \<in> ennreal ` A" thus "y \<le> ennreal (Sup A)"
    using assms cSup_upper ennreal_leI by auto
next
  fix y assume asm: "\<And>z. z \<in> ennreal ` A \<Longrightarrow> z \<le> y"
  show "ennreal (Sup A) \<le> y"
  proof (cases y)
    case (real r)
    show ?thesis      
      by (metis assms(1) cSup_le_iff ennreal_leI real(1) real(2) asm Sup_least bdd_above_top 
          cSUP_le_iff ennreal_le_iff nonempty)
  next
    case top
    thus ?thesis by auto
  qed
qed

lemma infsetsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
proof-
  have sum_F_A: "sum f F \<le> infsetsum f A" 
    if "F \<in> {F. finite F \<and> F \<subseteq> A}" 
    for F
  proof-
    from that have "finite F" and "F \<subseteq> A" by auto
    from \<open>finite F\<close> have "sum f F = infsetsum f F" by auto
    also have "\<dots> \<le> infsetsum f A"
    proof (rule infsetsum_mono_neutral_left)
      show "f abs_summable_on F"
        by (simp add: \<open>finite F\<close>)        
      show "f abs_summable_on A"
        by (simp add: local.summable)        
      show "f x \<le> f x"
        if "x \<in> F"
        for x :: 'a
        by simp 
      show "F \<subseteq> A"
        by (simp add: \<open>F \<subseteq> A\<close>)        
      show "0 \<le> f x"
        if "x \<in> A - F"
        for x :: 'a
        using that fnn by auto 
    qed
    finally show ?thesis by assumption
  qed 
  hence geq: "ennreal (infsetsum f A) \<ge> (SUP F\<in>{G. finite G \<and> G \<subseteq> A}. (ennreal (sum f F)))"
    by (meson SUP_least ennreal_leI)

  define fe where "fe x = ennreal (f x)" for x

  have sum_f_int: "infsetsum f A = \<integral>\<^sup>+ x. fe x \<partial>(count_space A)"
    unfolding infsetsum_def fe_def
  proof (rule nn_integral_eq_integral [symmetric])
    show "integrable (count_space A) f"
      using abs_summable_on_def local.summable by blast      
    show "AE x in count_space A. 0 \<le> f x"
      using fnn by auto      
  qed
  also have "\<dots> = (SUP g \<in> {g. finite (g`A) \<and> g \<le> fe}. integral\<^sup>S (count_space A) g)"
    unfolding nn_integral_def simple_function_count_space by simp
  also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
  proof (rule Sup_least)
    fix x assume "x \<in> integral\<^sup>S (count_space A) ` {g. finite (g ` A) \<and> g \<le> fe}"
    then obtain g where xg: "x = integral\<^sup>S (count_space A) g" and fin_gA: "finite (g`A)" 
      and g_fe: "g \<le> fe" by auto
    define F where "F = {z:A. g z \<noteq> 0}"
    hence "F \<subseteq> A" by simp

    have fin: "finite {z:A. g z = t}" if "t \<noteq> 0" for t
    proof (rule ccontr)
      assume inf: "infinite {z:A. g z = t}"
      hence tgA: "t \<in> g ` A"
        by (metis (mono_tags, lifting) image_eqI not_finite_existsD)
      have "x = (\<Sum>x \<in> g ` A. x * emeasure (count_space A) (g -` {x} \<inter> A))"
        unfolding xg simple_integral_def space_count_space by simp
      also have "\<dots> \<ge> (\<Sum>x \<in> {t}. x * emeasure (count_space A) (g -` {x} \<inter> A))" (is "_ \<ge> \<dots>")
      proof (rule sum_mono2)
        show "finite (g ` A)"
          by (simp add: fin_gA)          
        show "{t} \<subseteq> g ` A"
          by (simp add: tgA)          
        show "0 \<le> b * emeasure (count_space A) (g -` {b} \<inter> A)"
          if "b \<in> g ` A - {t}"
          for b :: ennreal
          using that
          by simp
      qed
      also have "\<dots> = t * emeasure (count_space A) (g -` {t} \<inter> A)"
        by auto
      also have "\<dots> = t * \<infinity>"
      proof (subst emeasure_count_space_infinite)
        show "g -` {t} \<inter> A \<subseteq> A"
          by simp             
        have "{a \<in> A. g a = t} = {a \<in> g -` {t}. a \<in> A}"
          by auto
        thus "infinite (g -` {t} \<inter> A)"
          by (metis (full_types) Int_def inf) 
        show "t * \<infinity> = t * \<infinity>"
          by simp
      qed
      also have "\<dots> = \<infinity>" using \<open>t \<noteq> 0\<close>
        by (simp add: ennreal_mult_eq_top_iff)
      finally have x_inf: "x = \<infinity>"
        using neq_top_trans by auto
      have "x = integral\<^sup>S (count_space A) g" by (fact xg)
      also have "\<dots> = integral\<^sup>N (count_space A) g"
        by (simp add: fin_gA nn_integral_eq_simple_integral)
      also have "\<dots> \<le> integral\<^sup>N (count_space A) fe"
        using g_fe
        by (simp add: le_funD nn_integral_mono)
      also have "\<dots> < \<infinity>"
        by (metis sum_f_int ennreal_less_top infinity_ennreal_def) 
      finally have x_fin: "x < \<infinity>" by simp
      from x_inf x_fin show False by simp
    qed
    have F: "F = (\<Union>t\<in>g`A-{0}. {z\<in>A. g z = t})"
      unfolding F_def by auto
    hence "finite F"
      unfolding F using fin_gA fin by auto
    have "x = integral\<^sup>N (count_space A) g"
      unfolding xg
      by (simp add: fin_gA nn_integral_eq_simple_integral)
    also have "\<dots> = set_nn_integral (count_space UNIV) A g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = set_nn_integral (count_space UNIV) F g"
    proof -
      have "\<forall>a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) = g a * (if a \<in> A then 1 else 0)"
        by auto
      hence "(\<integral>\<^sup>+ a. g a * (if a \<in> A then 1 else 0) \<partial>count_space UNIV)
           = (\<integral>\<^sup>+ a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) \<partial>count_space UNIV)"
        by presburger
      thus ?thesis unfolding F_def indicator_def
        using mult.right_neutral mult_zero_right nn_integral_cong
        by blast
    qed
    also have "\<dots> = integral\<^sup>N (count_space F) g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = sum g F" 
      using \<open>finite F\<close> by (rule nn_integral_count_space_finite)
    also have "sum g F \<le> sum fe F"
      using g_fe unfolding le_fun_def
      by (simp add: sum_mono) 
    also have "\<dots> \<le> (SUP F \<in> {G. finite G \<and> G \<subseteq> A}. (sum fe F))"
      using \<open>finite F\<close> \<open>F\<subseteq>A\<close>
      by (simp add: SUP_upper)
    also have "\<dots> = (SUP F \<in> {F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    proof (rule SUP_cong [OF refl])
      have "finite x \<Longrightarrow> x \<subseteq> A \<Longrightarrow> (\<Sum>x\<in>x. ennreal (f x)) = ennreal (sum f x)"
        for x
        by (metis fnn subsetCE sum_ennreal)
      thus "sum fe x = ennreal (sum f x)"
        if "x \<in> {G. finite G \<and> G \<subseteq> A}"
        for x :: "'a set"
        using that unfolding fe_def by auto      
    qed 
    finally show "x \<le> \<dots>" by simp
  qed
  finally have leq: "ennreal (infsetsum f A) \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    by assumption
  from leq geq show ?thesis by simp
qed

lemma infsetsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
proof -
  have "ereal (infsetsum f A) = enn2ereal (ennreal (infsetsum f A))"
    by (simp add: fnn infsetsum_nonneg)
  also have "\<dots> = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
  proof (subst infsetsum_nonneg_is_SUPREMUM_ennreal)
    show "f abs_summable_on A"
      by (simp add: local.summable)      
    show "0 \<le> f x"
      if "x \<in> A"
      for x :: 'a
      using that
      by (simp add: fnn) 
    show "enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F)) = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
      by simp      
  qed    
  also have "\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
  proof (simp add: image_def Sup_ennreal.rep_eq)
    have "0 \<le> Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x = ennreal (sum f xa)) \<and>
                     y = enn2ereal x}"
      by (metis (mono_tags, lifting) Sup_upper empty_subsetI ennreal_0 finite.emptyI
          mem_Collect_eq sum.empty zero_ennreal.rep_eq)
    moreover have "Sup {y. \<exists>x. (\<exists>y. finite y \<and> y \<subseteq> A \<and> x = ennreal (sum f y)) \<and>
                y = enn2ereal x} = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      using enn2ereal_ennreal fnn in_mono sum_nonneg Collect_cong
      by smt
    ultimately show "max 0 (Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x
                                       = ennreal (sum f xa)) \<and> y = enn2ereal x})
         = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      by linarith
  qed   
  finally show ?thesis
    by simp
qed

lemma infsetsum_nonneg_is_SUPREMUM:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
proof -
  have "ereal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
    using assms by (rule infsetsum_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
  proof (subst ereal_SUP)
    show "\<bar>SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a)\<bar> \<noteq> \<infinity>"
      using calculation by fastforce      
    show "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f F)) = (SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a))"
      by simp      
  qed
  finally show ?thesis by simp
qed

lemma infsetsum_geq0_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum f M \<ge> 0" (is "?lhs \<ge> _")
proof -
  have "?lhs \<ge> infsetsum (\<lambda>x. 0) M" (is "_ \<ge> \<dots>")
  proof (rule infsetsum_mono_complex)
    show "(\<lambda>x. 0::complex) abs_summable_on M"
      by simp      
    show "f abs_summable_on M"
      by (simp add: assms(1))      
    show "0 \<le> f x"
      if "x \<in> M"
      for x :: 'a
      using that
      using fnn by blast
  qed
  also have "\<dots> = 0"
    by auto
  finally show ?thesis by assumption
qed

lemma infsetsum_cmod:
  assumes "f abs_summable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum (\<lambda>x. cmod (f x)) M = cmod (infsetsum f M)"
proof -
  have nn: "infsetsum f M \<ge> 0" 
    using assms by (rule infsetsum_geq0_complex) 
  have "infsetsum (\<lambda>x. cmod (f x)) M = infsetsum (\<lambda>x. Re (f x)) M"
    using fnn cmod_eq_Re less_eq_complex_def by auto
  also have "\<dots> = Re (infsetsum f M)"
    using assms(1) infsetsum_Re by blast
  also have "\<dots> = cmod (infsetsum f M)" using nn cmod_eq_Re less_eq_complex_def by auto
  finally show ?thesis by assumption
qed

lemma infsetsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "f abs_summable_on (Sigma A B)"
  shows "infsetsum f (Sigma A B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) (B x)) A"
proof-
  from summable have countable_Sigma: "countable {x \<in> Sigma A B. 0 \<noteq> f x}"
    by (rule abs_summable_countable)
  define A' where "A' = fst ` {x \<in> Sigma A B. 0 \<noteq> f x}"
  have countA': "countable A'"
    using countable_Sigma unfolding A'_def by auto

  define B' where "B' a = snd ` ({x \<in> Sigma A B. 0 \<noteq> f x} \<inter> {(a,b) | b. True})" for a
  have countB': "countable (B' a)" for a
    using countable_Sigma unfolding B'_def by auto

  have Sigma_eq: "x \<in> Sigma A B \<longleftrightarrow> x \<in> Sigma A' B'" if "f x \<noteq> 0" for x
    unfolding A'_def B'_def Sigma_def 
    using that by force

  have Sigma'_smaller: "Sigma A' B' \<subseteq> Sigma A B"
    unfolding A'_def B'_def by auto
  with summable have summable': "f abs_summable_on Sigma A' B'"
    using abs_summable_on_subset by blast

  have A'_smaller: "A' \<subseteq> A"
    unfolding A'_def by auto
  have B'_smaller: "B' a \<subseteq> B a" for a
    unfolding B'_def by auto

  have "infsetsum f (Sigma A B) = infsetsum f (Sigma A' B')"
  proof (rule infsetsum_cong_neutral)
    show "f x = 0"
      if "x \<in> Sigma A B - Sigma A' B'"
      for x :: "'a \<times> 'b"
      using that
      by (meson DiffD1 DiffD2 Sigma_eq) 
    show "f x = 0"
      if "x \<in> Sigma A' B' - Sigma A B"
      for x :: "'a \<times> 'b"
      using that Sigma'_smaller by auto 
    show "f x = f x"
      if "x \<in> Sigma A B \<inter> Sigma A' B'"
      for x :: "'a \<times> 'b"
      using that
      by simp 
  qed 
  also from countA' countB' summable' have "\<dots> = (\<Sum>\<^sub>aa\<in>A'. \<Sum>\<^sub>ab\<in>B' a. f (a, b))"
    by (rule infsetsum_Sigma)
  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B' a. f (a, b))" (is "_ = (\<Sum>\<^sub>aa\<in>A. ?inner a)" is "_ = ?rhs")
  proof (rule infsetsum_cong_neutral)
    show "(\<Sum>\<^sub>ab\<in>B' x. f (x, b)) = 0"
      if "x \<in> A' - A"
      for x :: 'a
      using that A'_smaller by blast 
    show "(\<Sum>\<^sub>ab\<in>B' x. f (x, b)) = 0"
      if "x \<in> A - A'"
      for x :: 'a
    proof -
      have f1: "x \<in> A"
        by (metis DiffD1 that)
      obtain bb :: "('b \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> 'b" where
        "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> x0 v2 \<noteq> 0) = (bb x0 x1 \<in> x1 \<and> x0 (bb x0 x1) \<noteq> 0)"
        by moura
      hence f2: "\<forall>B f. bb f B \<in> B \<and> f (bb f B) \<noteq> 0 \<or> infsetsum f B = 0"
        by (meson infsetsum_all_0)
      have "(x, bb (\<lambda>b. f (x, b)) (B' x)) \<notin> Sigma A' B'"
        by (meson DiffD2 SigmaE2 that)
      thus ?thesis
        using f2 f1 by (meson B'_smaller SigmaI Sigma_eq in_mono)
    qed 
    show "(\<Sum>\<^sub>ab\<in>B' x. f (x, b)) = (\<Sum>\<^sub>ab\<in>B' x. f (x, b))"
      if "x \<in> A' \<inter> A"
      for x :: 'a
      using that
      by simp 
  qed
  also have "?inner a = (\<Sum>\<^sub>ab\<in>B a. f (a, b))" if "a\<in>A" for a
  proof (rule infsetsum_cong_neutral)
    show "f (a, x) = 0"
      if "x \<in> B' a - B a"
      for x :: 'b
      using that B'_smaller by blast 
    show "f (a, x) = 0"
      if "x \<in> B a - B' a"
      for x :: 'b
      using that Sigma_eq \<open>a \<in> A\<close> by fastforce 
    show "f (a, x) = f (a, x)"
      if "x \<in> B' a \<inter> B a"
      for x :: 'b
      using that
      by simp 
  qed
  hence "?rhs = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B a. f (a, b))"
    by (rule infsetsum_cong, auto)
  finally show ?thesis 
    by simp
qed

lemma infsetsum_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (Sigma A B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) (B x)) A = infsetsum (\<lambda>(x,y). f x y) (Sigma A B)"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times:
  fixes A :: "'a set" and B :: "'b set"
  assumes summable: "f abs_summable_on (A \<times> B)"
  shows   "infsetsum f (A \<times> B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) B) A"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times':
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (A \<times> B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
  using assms by (subst infsetsum_Times) auto

lemma infsetsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on A \<times> B"
  shows "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
proof-
  from summable have summable': "(\<lambda>(x,y). f y x) abs_summable_on B \<times> A"
    by (subst abs_summable_on_Times_swap) auto
  have bij: "bij_betw (\<lambda>(x, y). (y, x)) (B \<times> A) (A \<times> B)"
    by (auto simp: bij_betw_def inj_on_def)
  have "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
    using summable by (subst infsetsum_Times) auto
  also have "\<dots> = infsetsum (\<lambda>(x,y). f y x) (B \<times> A)"
    by (subst infsetsum_reindex_bij_betw[OF bij, of "\<lambda>(x,y). f x y", symmetric])
      (simp_all add: case_prod_unfold)
  also have "\<dots> = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
    using summable' by (subst infsetsum_Times) auto
  finally show ?thesis.
qed


lemma abs_summable_infsetsum'_converges:
  fixes f :: "'a\<Rightarrow>'b::{second_countable_topology,banach}" and A :: "'a set"
  assumes "f abs_summable_on A"
  shows "infsetsum'_converges f A"
proof-
  define F where "F = filtermap (sum f) (finite_subsets_at_top A)"
  have F_not_bot: "F \<noteq> bot"
    unfolding F_def filtermap_bot_iff by simp

  have "\<exists>P. eventually P (finite_subsets_at_top A) \<and> (\<forall>x y. P x \<and> P y
         \<longrightarrow> dist (sum f x) (sum f y) < e)"
    if "0 < e"
    for e :: real
  proof-
    have is_SUP: "ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x)))"
    proof (rule infsetsum_nonneg_is_SUPREMUM_ereal)
      show "(\<lambda>x. norm (f x)) abs_summable_on A"
        by (simp add: assms)

      show "0 \<le> norm (f x)"
        if "x \<in> A"
        for x :: 'a
        using that
        by simp 
    qed 
    have "\<exists>F0\<in>{F. finite F \<and> F \<subseteq> A}.
       (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x))) - ereal e
       < ereal (\<Sum>x\<in>F0. norm (f x))"
      unfolding is_SUP Bex_def[symmetric]
      by (smt less_SUP_iff[symmetric] \<open>0 < e\<close> ereal_diff_le_self ereal_less_eq(5) ereal_minus(1) 
          is_SUP less_eq_ereal_def)
    then obtain F0 where "F0\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (\<Sum>x\<in>F0. norm (f x)) > ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) - ereal e"
      by (simp add: atomize_elim is_SUP) 
    hence [simp]: "finite F0" and [simp]: "F0 \<subseteq> A" 
      and sum_diff: "sum (\<lambda>x. norm (f x)) F0 > infsetsum (\<lambda>x. norm (f x)) A - e"
      by auto
    define P where "P F \<longleftrightarrow> finite F \<and> F \<supseteq> F0 \<and> F \<subseteq> A" for F
    have "dist (sum f F1) (sum f F2) < e" if "P F1" and "P F2" for F1 F2
    proof -
      from that(1) have "finite F1" and "F1 \<supseteq> F0" and "F1 \<subseteq> A" unfolding P_def by auto
      from that(2) have "finite F2" and "F2 \<supseteq> F0" and "F2 \<subseteq> A" unfolding P_def by auto
      have "dist (sum f F1) (sum f F2) = norm (sum f (F1-F2) - sum f (F2-F1))"
        unfolding dist_norm
        by (smt \<open>finite F1\<close> \<open>finite F2\<close> add_diff_cancel_left' add_diff_cancel_right' algebra_simps sum.Int_Diff sum.union_diff2 sum.union_inter) 
      also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) (F1-F2) + sum (\<lambda>x. norm (f x)) (F2-F1)"
        by (smt norm_triangle_ineq4 sum_norm_le)
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) (F1-F2) + infsetsum (\<lambda>x. norm (f x)) (F2-F1)"
        by (simp add: \<open>finite F1\<close> \<open>finite F2\<close>)
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) ((F1-F2)\<union>(F2-F1))"
      proof (rule infsetsum_Un_disjoint [symmetric])
        show "(\<lambda>x. norm (f x)) abs_summable_on F1 - F2"
          by (simp add: \<open>finite F1\<close>)          
        show "(\<lambda>x. norm (f x)) abs_summable_on F2 - F1"
          by (simp add: \<open>finite F2\<close>)          
        show "(F1 - F2) \<inter> (F2 - F1) = {}"
          by (simp add: Diff_Int_distrib2)          
      qed
      also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F0)"
      proof (rule infsetsum_mono_neutral_left)
        show "(\<lambda>x. norm (f x)) abs_summable_on F1 - F2 \<union> (F2 - F1)"
          by (simp add: \<open>finite F1\<close> \<open>finite F2\<close>)          
        show "(\<lambda>x. norm (f x)) abs_summable_on A - F0"
          using abs_summable_on_subset assms by fastforce          
        show "norm (f x) \<le> norm (f x)"
          if "x \<in> F1 - F2 \<union> (F2 - F1)"
          for x :: 'a
          using that
          by simp 
        show "F1 - F2 \<union> (F2 - F1) \<subseteq> A - F0"
          by (simp add: Diff_mono \<open>F0 \<subseteq> F1\<close> \<open>F0 \<subseteq> F2\<close> \<open>F1 \<subseteq> A\<close> \<open>F2 \<subseteq> A\<close>)          
        show "0 \<le> norm (f x)"
          if "x \<in> A - F0 - (F1 - F2 \<union> (F2 - F1))"
          for x :: 'a
          by simp 
      qed
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) A - infsetsum (\<lambda>x. norm (f x)) F0"
        by (simp add: assms infsetsum_Diff)
      also have "\<dots> < e"
        using local.sum_diff by auto
      finally show "dist (sum f F1) (sum f F2) < e" by assumption
    qed
    moreover have "eventually P (finite_subsets_at_top A)"
      unfolding P_def eventually_finite_subsets_at_top
      using \<open>F0 \<subseteq> A\<close> \<open>finite F0\<close> by blast      
    ultimately show "\<exists>P. eventually P (finite_subsets_at_top A) \<and> (\<forall>F1 F2. P F1 \<and> P F2 \<longrightarrow> dist (sum f F1) (sum f F2) < e)"
      by auto
  qed
  hence cauchy: "cauchy_filter F"
    unfolding F_def
    by (rule cauchy_filter_metric_filtermapI)  
  from complete_UNIV have "F\<le>principal UNIV \<Longrightarrow> F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> (\<exists>x. F \<le> nhds x)"
    unfolding complete_uniform
    by auto
  have "(F \<le> principal UNIV \<Longrightarrow> F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> \<exists>x. F \<le> nhds x) \<Longrightarrow>
    \<exists>x. F \<le> nhds x"
    using cauchy F_not_bot by simp
  then obtain x where Fx: "F \<le> nhds x"
    using \<open>\<lbrakk>F \<le> principal UNIV; F \<noteq> bot; cauchy_filter F\<rbrakk> \<Longrightarrow> \<exists>x. F \<le> nhds x\<close> by blast
  hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding F_def
    by (simp add: filterlim_def)
  thus ?thesis
    unfolding infsetsum'_converges_def by auto
qed

lemma infsetsum'_converges_cofin_subset:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "infsetsum'_converges f A" and [simp]: "finite F"
  shows "infsetsum'_converges f (A-F)"
proof-
  from assms(1) obtain x where lim_f: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding infsetsum'_converges_def by auto
  define F' where "F' = F\<inter>A"
  with assms have "finite F'" and "A-F = A-F'"
    by auto
  have "filtermap ((\<union>)F') (finite_subsets_at_top (A-F))
      \<le> finite_subsets_at_top A"
  proof (rule filter_leI)
    fix P assume "eventually P (finite_subsets_at_top A)"
    then obtain X where [simp]: "finite X" and XA: "X \<subseteq> A" 
      and P: "\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P Y"
      unfolding eventually_finite_subsets_at_top by auto
    define X' where "X' = X-F"
    hence [simp]: "finite X'" and [simp]: "X' \<subseteq> A-F"
      using XA by auto
    hence "finite Y \<and> X' \<subseteq> Y \<and> Y \<subseteq> A - F \<longrightarrow> P (F' \<union> Y)" for Y
      using P XA unfolding X'_def using F'_def \<open>finite F'\<close> by blast
    thus "eventually P (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))"
      unfolding eventually_filtermap eventually_finite_subsets_at_top
      by (rule_tac x=X' in exI, simp)
  qed
  with lim_f have "(sum f \<longlongrightarrow> x) (filtermap ((\<union>)F') (finite_subsets_at_top (A-F)))"
    using tendsto_mono by blast
  have "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    if "((sum f \<circ> (\<union>) F') \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    using that unfolding o_def by auto
  hence "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_compose_filtermap [symmetric]
    by (simp add: \<open>(sum f \<longlongrightarrow> x) (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))\<close> 
        tendsto_compose_filtermap)
  have "\<forall>Y. finite Y \<and> Y \<subseteq> A - F \<longrightarrow> sum f (F' \<union> Y) = sum f F' + sum f Y"
    by (metis Diff_disjoint Int_Diff \<open>A - F = A - F'\<close> \<open>finite F'\<close> inf.orderE sum.union_disjoint)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top (A - F). sum f (F' \<union> x) = sum f F' + sum f x"
    unfolding eventually_finite_subsets_at_top
    using exI [where x = "{}"]
    by (simp add: \<open>\<And>P. P {} \<Longrightarrow> \<exists>x. P x\<close>) 
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))\<close> by fastforce
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> sum f F' + (x-sum f F')) (finite_subsets_at_top (A-F))"
    by simp
  hence "(sum f \<longlongrightarrow> x - sum f F') (finite_subsets_at_top (A-F))"
    using Extra_General.tendsto_add_const_iff by blast    
  thus "infsetsum'_converges f (A - F)"
    unfolding infsetsum'_converges_def by auto
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,t2_space}"
  assumes "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0"
  shows infsetsum'_subset_zero: "infsetsum' f A = infsetsum' f B"
    and infsetsum'_converges_subset_zero: "infsetsum'_converges f A = infsetsum'_converges f B"
proof -
  have convB: "infsetsum'_converges f B" and eq: "infsetsum' f A = infsetsum' f B"
    if convA: "infsetsum'_converges f A" and f0: "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0" for A B
  proof -
    define D where "D = (A-B)"
    define D' where "D' = B-A"

    from convA obtain x where limA: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
      using infsetsum'_converges_def by blast
    have "sum f X = sum f (X - D)"
      if "finite (X::'a set)"
        and "X \<subseteq> A"
      for X :: "'a set"
      using that f0 D_def by (simp add: subset_iff sum.mono_neutral_cong_right)
    hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum f (x - D)"
      by (rule eventually_finite_subsets_at_top_weakI)
    hence "((\<lambda>F. sum f (F-D)) \<longlongrightarrow> x) (finite_subsets_at_top A)"
      using tendsto_cong [THEN iffD1, rotated] limA by fastforce
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F-D) (finite_subsets_at_top A))"
      by (simp add: filterlim_filtermap)
    have "D \<subseteq> A"
      unfolding D_def by simp
    hence "finite_subsets_at_top (A - D) \<le> filtermap (\<lambda>F. F - D) (finite_subsets_at_top A)"
      by (rule finite_subsets_at_top_minus)
    hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top (A-D))"
      using tendsto_mono [rotated] 
        \<open>(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F - D) (finite_subsets_at_top A))\<close>
      by blast
    have "A - D \<subseteq> B"
      unfolding D_def by auto
    hence "filtermap (\<lambda>F. F \<inter> (A - D)) (finite_subsets_at_top B) \<le> finite_subsets_at_top (A - D)"
      by (rule finite_subsets_at_top_inter [where B = B and A = "A-D"])
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F \<inter> (A - D)) (finite_subsets_at_top B))"
      using tendsto_mono [rotated] \<open>(sum f \<longlongrightarrow> x) (finite_subsets_at_top (A - D))\<close> by blast
    hence "((\<lambda>F. sum f (F \<inter> (A - D))) \<longlongrightarrow> x) (finite_subsets_at_top B)"
      by (simp add: filterlim_filtermap)
    have "sum f (X \<inter> (A - D)) = sum f X"
      if "finite (X::'a set)"
        and "X \<subseteq> B"
      for X :: "'a set"
    proof (rule sum.mono_neutral_cong)
      show "finite X"
        by (simp add: that(1))
      show "finite (X \<inter> (A - D))"
        by (simp add: that(1))
      show "f i = 0"
        if "i \<in> X - X \<inter> (A - D)"
        for i :: 'a
        using that D_def DiffD2 \<open>X \<subseteq> B\<close> f0 by auto 
      show "f i = 0"
        if "i \<in> X \<inter> (A - D) - X"
        for i :: 'a
        using that
        by auto 
      show "f x = f x"
        if "x \<in> X \<inter> (A - D) \<inter> X"
        for x :: 'a
        by simp
    qed
    hence "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f (x \<inter> (A - D)) = sum f x"
      by (rule eventually_finite_subsets_at_top_weakI)      
    hence limB: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top B)"
      using tendsto_cong [THEN iffD1 , rotated]
        \<open>((\<lambda>F. sum f (F \<inter> (A - D))) \<longlongrightarrow> x) (finite_subsets_at_top B)\<close> by blast
    thus "infsetsum'_converges f B"
      unfolding infsetsum'_converges_def by auto
    have "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top B) (sum f)"
      if "infsetsum'_converges f B"
      using that    using limA limB
      using finite_subsets_at_top_neq_bot tendsto_Lim by blast
    thus "infsetsum' f A = infsetsum' f B"
      unfolding infsetsum'_def 
      using convA
      by (simp add: \<open>infsetsum'_converges f B\<close>)
  qed
  with assms show "infsetsum'_converges f A = infsetsum'_converges f B"
    by (metis Un_commute)
  thus "infsetsum' f A = infsetsum' f B"
    using assms convB eq
    by (metis infsetsum'_def)
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "infsetsum'_converges f B" and "infsetsum'_converges f A" and AB: "A \<subseteq> B"
  shows infsetsum'_Diff: "infsetsum' f (B - A) = infsetsum' f B - infsetsum' f A"
    and infsetsum'_converges_Diff: "infsetsum'_converges f (B-A)"
proof -
  define limA limB where "limA = infsetsum' f A" and "limB = infsetsum' f B"
  from assms(1) have limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    unfolding infsetsum'_converges_def infsetsum'_def limB_def
    by (auto simp: tendsto_Lim)
  from assms(2) have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)"
    unfolding infsetsum'_converges_def infsetsum'_def limA_def
    by (auto simp: tendsto_Lim)
  have "((\<lambda>F. sum f (F\<inter>A)) \<longlongrightarrow> limA) (finite_subsets_at_top B)"
  proof (subst asm_rl [of "(\<lambda>F. sum f (F\<inter>A)) = sum f o (\<lambda>F. F\<inter>A)"])
    show "(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)"
      unfolding o_def by auto
    show "((sum f \<circ> (\<lambda>F. F \<inter> A)) \<longlongrightarrow> limA) (finite_subsets_at_top B)"
      unfolding o_def 
      using tendsto_compose_filtermap finite_subsets_at_top_inter[OF AB] limA tendsto_mono
        \<open>(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)\<close> by fastforce
  qed
  with limB have "((\<lambda>F. sum f F - sum f (F\<inter>A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    using tendsto_diff by blast
  have "sum f X - sum f (X \<inter> A) = sum f (X - A)"
    if "finite (X::'a set)"
      and "X \<subseteq> B"
    for X :: "'a set"
    using that by (metis add_diff_cancel_left' sum.Int_Diff)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f x - sum f (x \<inter> A) = sum f (x - A)"
    by (rule eventually_finite_subsets_at_top_weakI)  
  hence "((\<lambda>F. sum f (F-A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>F. sum f F - sum f (F \<inter> A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)\<close> by fastforce
  hence "(sum f \<longlongrightarrow> limB - limA) (filtermap (\<lambda>F. F-A) (finite_subsets_at_top B))"
    by (subst tendsto_compose_filtermap[symmetric], simp add: o_def)
  hence limBA: "(sum f \<longlongrightarrow> limB - limA) (finite_subsets_at_top (B-A))"
    using finite_subsets_at_top_minus[OF AB] by (rule tendsto_mono[rotated])
  thus "infsetsum'_converges f (B-A)"
    unfolding infsetsum'_converges_def by auto
  with limBA show "infsetsum' f (B - A) = limB - limA"
    unfolding infsetsum'_def by (simp add: tendsto_Lim) 
qed

lemma infsetsum'_mono_set:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes fx0: "\<And>x. x\<in>B-A \<Longrightarrow> f x \<ge> 0"
    and "A \<subseteq> B"
    and "infsetsum'_converges f A"
    and "infsetsum'_converges f B"
  shows "infsetsum' f B \<ge> infsetsum' f A"
proof -
  define limA limB f' where "limA = infsetsum' f A" and "limB = infsetsum' f B"
    and "f' x = (if x \<in> A then f x else 0)" for x
  have "infsetsum' f A = infsetsum' f' B"
  proof (subst infsetsum'_subset_zero [where f = f' and B = A])
    show "f' x = 0"
      if "x \<in> B - A \<union> (A - B)"
      for x :: 'a
      using that assms(2) f'_def by auto 
    show "infsetsum' f A = infsetsum' f' A"
      by (metis f'_def infsetsum'_cong)      
  qed
  hence limA_def': "limA = infsetsum' f' B"
    unfolding limA_def
    by auto
  have convA': "infsetsum'_converges f' B"
  proof (rule infsetsum'_converges_subset_zero [THEN iffD1 , where A1 = A])
    show "f' x = 0"
      if "x \<in> A - B \<union> (B - A)"
      for x :: 'a
      using that assms(2) f'_def by auto 
    show "infsetsum'_converges f' A"
      by (simp add: assms(3) f'_def infsetsum'_converges_cong)      
  qed
  from assms have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)" 
    and limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    by (auto simp: limA_def limB_def infsetsum'_converges_def infsetsum'_def tendsto_Lim)
  have limA': "(sum f' \<longlongrightarrow> limA) (finite_subsets_at_top B)"
    using finite_subsets_at_top_neq_bot tendsto_Lim convA'
    unfolding limA_def' infsetsum'_def  infsetsum'_converges_def
    by fastforce 
  have "f' i \<le> f i"
    if "i \<in> X" and "X \<subseteq> B"
    for i :: 'a and X
    unfolding f'_def using fx0 that
    using \<open>X \<subseteq> B\<close> by auto
  hence "sum f' X \<le> sum f X"
    if "finite (X::'a set)"
      and "X \<subseteq> B"
    for X :: "'a set"
    using sum_mono
    by (simp add: sum_mono that(2)) 
  hence sumf'_leq_sumf: "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f' x \<le> sum f x"
    by (rule eventually_finite_subsets_at_top_weakI)
  show "limA \<le> limB"
    using finite_subsets_at_top_neq_bot limB limA' sumf'_leq_sumf 
    by (rule tendsto_le)
qed

lemma infsetsum'_converges_finite[simp]:
  assumes "finite F"
  shows "infsetsum'_converges f F"
  unfolding infsetsum'_converges_def finite_subsets_at_top_finite[OF assms]
  using tendsto_principal_singleton by fastforce 

lemma infsetsum'_finite[simp]:
  assumes "finite F"
  shows "infsetsum' f F = sum f F"
  using assms by (auto intro: tendsto_Lim simp: finite_subsets_at_top_finite infsetsum'_def principal_eq_bot_iff tendsto_principal_singleton)

lemma infsetsum'_approx_sum:
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,metric_space}"
  assumes "infsetsum'_converges f A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsetsum' f A) \<le> \<epsilon>"
proof-
  have "infsetsum'_converges f A \<Longrightarrow>
    0 < \<epsilon> \<Longrightarrow> (sum f \<longlongrightarrow> Lim (finite_subsets_at_top A) (sum f)) (finite_subsets_at_top A)"
    unfolding infsetsum'_converges_def
    using Lim_trivial_limit tendsto_Lim by blast
  hence "(sum f \<longlongrightarrow> infsetsum' f A) (finite_subsets_at_top A)"
    unfolding infsetsum'_def
    using assms
    by simp
  hence "\<forall>\<^sub>F F in (finite_subsets_at_top A). dist (sum f F) (infsetsum' f A) < \<epsilon>"
    using assms(2) by (rule tendstoD)
  have "finite X \<Longrightarrow>
         X \<subseteq> A \<Longrightarrow>
         \<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> dist (sum f Y) (infsetsum' f A) < \<epsilon> \<Longrightarrow>
         \<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsetsum' f A) \<le> \<epsilon>"
    for X
    by fastforce    
  thus ?thesis
    using eventually_finite_subsets_at_top
    by (metis (no_types, lifting)
        \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. dist (sum f F) (infsetsum' f A) < \<epsilon>\<close>)
qed

lemma norm_infsetsum'_bound:
  fixes f :: "'b \<Rightarrow> 'a::real_normed_vector"
    and A :: "'b set"
  assumes a1: "infsetsum'_converges (\<lambda>x. norm (f x)) A"
  shows "norm (infsetsum' f A) \<le> (infsetsum' (\<lambda>x. norm (f x)) A)"
proof(cases "infsetsum'_converges f A")
  case True
  have "norm (infsetsum' f A) \<le> (infsetsum' (\<lambda>x. norm (f x)) A) + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof-
    have "\<exists>F. norm (infsetsum' f A - sum f F) \<le> \<epsilon> \<and> finite F \<and> F \<subseteq> A"
      using infsetsum'_approx_sum[where A=A and f=f and \<epsilon>="\<epsilon>"] a1 True \<open>0 < \<epsilon>\<close>
      by (metis dist_commute dist_norm)
    then obtain F where "norm (infsetsum' f A - sum f F) \<le> \<epsilon>"
      and "finite F" and "F \<subseteq> A"
      by (simp add: atomize_elim)
    hence "norm (infsetsum' f A) \<le> norm (sum f F) + \<epsilon>"
      by (smt norm_triangle_sub)
    also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) F + \<epsilon>"
      using norm_sum by auto
    also have "\<dots> \<le> (infsetsum' (\<lambda>x. norm (f x)) A) + \<epsilon>"
    proof-
      have "infsetsum' (\<lambda>x. norm (f x)) F \<le> infsetsum' (\<lambda>x. norm (f x)) A"
      proof (rule infsetsum'_mono_set)
        show "0 \<le> norm (f x)"
          if "x \<in> A - F"
          for x :: 'b
          using that
          by simp 
        show "F \<subseteq> A"
          by (simp add: \<open>F \<subseteq> A\<close>)          
        show "infsetsum'_converges (\<lambda>x. norm (f x)) F"
          using \<open>finite F\<close> by auto         
        show "infsetsum'_converges (\<lambda>x. norm (f x)) A"
          by (simp add: assms)          
      qed
      thus ?thesis
        by (simp_all flip: infsetsum'_finite add: \<open>finite F\<close>)
    qed
    finally show ?thesis 
      by assumption
  qed
  thus ?thesis
    using linordered_field_class.field_le_epsilon by blast
next
  case False
  obtain t where t_def: "(sum (\<lambda>x. norm (f x)) \<longlongrightarrow> t) (finite_subsets_at_top A)"
    using a1 unfolding infsetsum'_converges_def by blast
  have sumpos: "sum (\<lambda>x. norm (f x)) X \<ge> 0"
    for X
    by (simp add: sum_nonneg)
  have tgeq0:"t \<ge> 0"
  proof(rule ccontr)
    define S::"real set" where "S = {s. s < 0}"
    assume "\<not> 0 \<le> t"
    hence "t < 0" by simp
    hence "t \<in> S"
      unfolding S_def by blast
    moreover have "open S"
    proof-
      have "closed {s::real. s \<ge> 0}"
        using Elementary_Topology.closed_sequential_limits[where S = "{s::real. s \<ge> 0}"]
        by (metis Lim_bounded2 mem_Collect_eq)
      moreover have "{s::real. s \<ge> 0} = UNIV - S"
        unfolding S_def by auto
      ultimately have "closed (UNIV - S)"
        by simp
      thus ?thesis
        by (simp add: Compl_eq_Diff_UNIV open_closed) 
    qed
    ultimately have "\<forall>\<^sub>F X in finite_subsets_at_top A. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      using t_def unfolding tendsto_def by blast
    hence "\<exists>X. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      by (metis (no_types, lifting) False eventually_mono filterlim_iff infsetsum'_converges_def)
    then obtain X where "(\<Sum>x\<in>X. norm (f x)) \<in> S"
      by blast
    hence "(\<Sum>x\<in>X. norm (f x)) < 0"
      unfolding S_def by auto      
    thus False using sumpos by smt
  qed
  have "\<exists>!h. (sum (\<lambda>x. norm (f x)) \<longlongrightarrow> h) (finite_subsets_at_top A)"
    using t_def finite_subsets_at_top_neq_bot tendsto_unique by blast
  hence "t = (Topological_Spaces.Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))))"
    using t_def unfolding Topological_Spaces.Lim_def
    by (metis the_equality)     
  hence "Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))) \<ge> 0"
    using tgeq0 by blast
  thus ?thesis unfolding infsetsum'_def 
    using False by auto
qed


lemma infsetsum_infsetsum':
  assumes "f abs_summable_on A"
  shows "infsetsum f A = infsetsum' f A"
proof-
  have conv_sum_norm[simp]: "infsetsum'_converges (\<lambda>x. norm (f x)) A"
  proof (rule abs_summable_infsetsum'_converges)
    show "(\<lambda>x. norm (f x)) abs_summable_on A"
      using assms by simp
  qed    
  have "norm (infsetsum f A - infsetsum' f A) \<le> \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof -
    define \<delta> where "\<delta> = \<epsilon>/2"
    with that have [simp]: "\<delta> > 0" by simp
    obtain F1 where F1A: "F1 \<subseteq> A" and finF1: "finite F1" and leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F1) \<le> \<delta>"
    proof -
      have sum_SUP: "ereal (infsetsum (\<lambda>x. norm (f x)) A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum (\<lambda>x. norm (f x)) F))"
        (is "_ = ?SUP")
      proof (rule infsetsum_nonneg_is_SUPREMUM_ereal)
        show "(\<lambda>x. norm (f x)) abs_summable_on A"
          by (simp add: assms)          
        show "0 \<le> norm (f x)"
          if "x \<in> A"
          for x :: 'a
          using that
          by simp 
      qed

      have "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x))) - ereal \<delta>
    < (SUP i\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>i. norm (f x)))"
        using \<open>\<delta>>0\<close>
        by (metis diff_strict_left_mono diff_zero ereal_less_eq(3) ereal_minus(1) not_le sum_SUP)
      then obtain F where "F\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (sum (\<lambda>x. norm (f x)) F) > ?SUP - ereal (\<delta>)"
        by (meson less_SUP_iff)

      hence "sum (\<lambda>x. norm (f x)) F > infsetsum (\<lambda>x. norm (f x)) A -  (\<delta>)"
        unfolding sum_SUP[symmetric] by auto
      hence "\<delta> > infsetsum (\<lambda>x. norm (f x)) (A-F)"
      proof (subst infsetsum_Diff)
        show "(\<lambda>x. norm (f x)) abs_summable_on A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that
          by (simp add: assms) 
        show "F \<subseteq> A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by blast 
        show "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - (\<Sum>\<^sub>ax\<in>F. norm (f x)) < \<delta>"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by auto 
      qed
      thus ?thesis using that 
        apply atomize_elim
        using \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> less_imp_le by blast
    qed
    have "\<exists>F2\<subseteq>A.
       finite F2 \<and>
       dist (\<Sum>x\<in>F2. norm (f x)) (infsetsum' (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      using infsetsum'_approx_sum[where f="(\<lambda>x. norm (f x))" and A=A and \<epsilon>=\<delta>]
        abs_summable_infsetsum'_converges assms by auto
    then obtain F2 where F2A: "F2 \<subseteq> A" and finF2: "finite F2"
      and dist: "dist (sum (\<lambda>x. norm (f x)) F2) (infsetsum' (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      by blast     
    have  leq_eps': "infsetsum' (\<lambda>x. norm (f x)) (A-F2) \<le> \<delta>"
    proof (subst infsetsum'_Diff)
      show "infsetsum'_converges (\<lambda>x. norm (f x)) A"
        by simp        
      show "infsetsum'_converges (\<lambda>x. norm (f x)) F2"
        by (simp add: finF2)        
      show "F2 \<subseteq> A"
        by (simp add: F2A)        
      show "infsetsum' (\<lambda>x. norm (f x)) A - infsetsum' (\<lambda>x. norm (f x)) F2 \<le> \<delta>"
        using dist finF2
        by (auto simp: dist_norm)
    qed 
    define F where "F = F1 \<union> F2"
    have FA: "F \<subseteq> A" and finF: "finite F" 
      unfolding F_def using F1A F2A finF1 finF2 by auto

    have "(\<Sum>\<^sub>ax\<in>A - (F1 \<union> F2). norm (f x)) \<le> (\<Sum>\<^sub>ax\<in>A - F1. norm (f x))"
    proof (rule infsetsum_mono_neutral_left)
      show "(\<lambda>x. norm (f x)) abs_summable_on A - (F1 \<union> F2)"
        using abs_summable_on_subset assms by fastforce        
      show "(\<lambda>x. norm (f x)) abs_summable_on A - F1"
        using abs_summable_on_subset assms by fastforce        
      show "norm (f x) \<le> norm (f x)"
        if "x \<in> A - (F1 \<union> F2)"
        for x :: 'a
        using that
        by auto 
      show "A - (F1 \<union> F2) \<subseteq> A - F1"
        by (simp add: Diff_mono)        
      show "0 \<le> norm (f x)"
        if "x \<in> A - F1 - (A - (F1 \<union> F2))"
        for x :: 'a
        using that
        by auto 
    qed
    hence leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def
      using leq_eps by linarith
    have "infsetsum' (\<lambda>x. norm (f x)) (A - (F1 \<union> F2))
    \<le> infsetsum' (\<lambda>x. norm (f x)) (A - F2)"
    proof (rule infsetsum'_mono_set)
      show "0 \<le> norm (f x)"
        if "x \<in> A - F2 - (A - (F1 \<union> F2))"
        for x :: 'a
        using that
        by simp 
      show "A - (F1 \<union> F2) \<subseteq> A - F2"
        by (simp add: Diff_mono)        
      show "infsetsum'_converges (\<lambda>x. norm (f x)) (A - (F1 \<union> F2))"
        using F_def conv_sum_norm finF infsetsum'_converges_cofin_subset by blast        
      show "infsetsum'_converges (\<lambda>x. norm (f x)) (A - F2)"
        by (simp add: finF2 infsetsum'_converges_cofin_subset)        
    qed
    hence leq_eps': "infsetsum' (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def 
      by (rule order.trans[OF _ leq_eps'])
    have "norm (infsetsum f A - infsetsum f F) = norm (infsetsum f (A-F))"
    proof (subst infsetsum_Diff [symmetric])
      show "f abs_summable_on A"
        by (simp add: assms)          
      show "F \<subseteq> A"
        by (simp add: FA)          
      show "norm (infsetsum f (A - F)) = norm (infsetsum f (A - F))"
        by simp          
    qed
    also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F)"
      using norm_infsetsum_bound by blast
    also have "\<dots> \<le> \<delta>"
      using leq_eps by simp
    finally have diff1: "norm (infsetsum f A - infsetsum f F) \<le> \<delta>"
      by assumption
    have "norm (infsetsum' f A - infsetsum' f F) = norm (infsetsum' f (A-F))"
    proof (subst infsetsum'_Diff [symmetric])
      show "infsetsum'_converges f A"
        by (simp add: abs_summable_infsetsum'_converges assms)        
      show "infsetsum'_converges f F"
        by (simp add: finF)        
      show "F \<subseteq> A"
        by (simp add: FA)        
      show "norm (infsetsum' f (A - F)) = norm (infsetsum' f (A - F))"
        by simp        
    qed
    also have "\<dots> \<le> infsetsum' (\<lambda>x. norm (f x)) (A-F)"
      by (simp add: finF infsetsum'_converges_cofin_subset norm_infsetsum'_bound)
    also have "\<dots> \<le> \<delta>"
      using leq_eps' by simp
    finally have diff2: "norm (infsetsum' f A - infsetsum' f F) \<le> \<delta>"
      by assumption

    have x1: "infsetsum f F = infsetsum' f F"
      using finF by simp
    have "norm (infsetsum f A - infsetsum' f A) \<le> norm (infsetsum f A - infsetsum f F) + norm (infsetsum' f A - infsetsum' f F)"
      apply (rule_tac norm_diff_triangle_le)
       apply auto
      by (simp_all add: x1 norm_minus_commute)
    also have "\<dots> \<le> \<epsilon>"
      using diff1 diff2 \<delta>_def by linarith
    finally show ?thesis
      by assumption
  qed
  hence "norm (infsetsum f A - infsetsum' f A) = 0"
    by (meson antisym_conv1 dense_ge norm_not_less_zero)
  thus ?thesis
    by auto
qed

lemma abs_summable_partition:
  fixes T :: "'b set" and I :: "'a set"
  assumes "\<And>i. f abs_summable_on S i"
    and "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on I"
    and "T \<subseteq> (\<Union>i\<in>I. S i)"
  shows "f abs_summable_on T"
proof (rule abs_summable_finiteI)
  fix F assume finite_F: "finite F" and FT: "F \<subseteq> T"
  define index where "index s = (SOME i. i\<in>I \<and> s\<in>S i)" for s
  hence index_I: "index s \<in> I" and S_index: "s \<in> S (index s)" if "s \<in> (\<Union>i\<in>I. S i)" for s
  proof auto
    show "(SOME i. i \<in> I \<and> s \<in> S i) \<in> I"
      if "\<And>s. index s = (SOME i. i \<in> I \<and> s \<in> S i)"
      using that
      by (metis (no_types, lifting) UN_iff \<open>s \<in> \<Union> (S ` I)\<close> someI_ex) 
    show "s \<in> S (SOME i. i \<in> I \<and> s \<in> S i)"
      if "\<And>s. index s = (SOME i. i \<in> I \<and> s \<in> S i)"
      using that
      by (metis (no_types, lifting) UN_iff \<open>s \<in> \<Union> (S ` I)\<close> someI_ex) 
  qed
  define S' where "S' i = {s\<in>S i. i = index s}" for i
  have S'_S: "S' i \<subseteq> S i" for i
    unfolding S'_def by simp
  hence f_sum_S': "f abs_summable_on S' i" for i
    by (meson abs_summable_on_subset assms(1))
  with assms(1) S'_S have "(\<Sum>\<^sub>ax\<in>S' i. norm (f x)) \<le> (\<Sum>\<^sub>ax\<in>S i. norm (f x))" for i
    by (simp add: infsetsum_mono_neutral_left)
  with assms(2) have sum_I: "(\<lambda>i. \<Sum>\<^sub>ax\<in>S' i. norm (f x)) abs_summable_on I"
    by (smt abs_summable_on_comparison_test' infsetsum_cong norm_ge_zero norm_infsetsum_bound real_norm_def)
  have "(\<Union>i\<in>I. S i) = (\<Union>i\<in>I. S' i)"
    unfolding S'_def by (auto intro!: index_I S_index)
  with assms(3) have T_S': "T \<subseteq> (\<Union>i\<in>I. S' i)"
    by simp
  have S'_disj: "(S' i) \<inter> (S' j) = {}" if "i\<noteq>j" for i j
    unfolding S'_def disjnt_def using that by auto

  define B where "B i = (\<Sum>\<^sub>ax\<in>S i. norm (f x))" for i
  have sum_FS'_B: "(\<Sum>x\<in>F\<inter>S' i. norm (f x)) \<le> B i" for i
    unfolding B_def using f_sum_S' finite_F FT
    by (metis S'_S abs_summable_finiteI_converse assms(1) finite_Int le_inf_iff order_refl 
        subset_antisym)
  have B_pos[simp]: "B i \<ge> 0" for i
    unfolding B_def by (rule infsetsum_nonneg, simp)
  have B_sum_I[simp]: "B abs_summable_on I"
    by (simp add: B_def assms(2))
  define J where "J = {i\<in>I. F\<inter>S' i \<noteq> {}}"
  have finite_J[simp]: "finite J"
  proof -
    define a where "a i = (SOME x. x\<in>F\<inter>S' i)" for i
    hence a: "a i \<in> F\<inter>S' i" if "i \<in> J" for i
      unfolding J_def
      by (metis (mono_tags) Collect_conj_eq Int_Collect J_def some_in_eq that)
    have xy: "x = y"
      if "x \<in> J" and "y \<in> J" and "a x = a y" and "\<And>i. i \<in> J \<Longrightarrow> a i \<in> F \<and> a i \<in> S' i"
        and "\<And>i j. i \<noteq> j \<Longrightarrow> S' i \<inter> S' j = {}"
        for x y     
      using that a S'_disj
      by (metis S'_disj disjoint_iff_not_equal)
    hence "inj_on a J"
      unfolding inj_on_def
      using S'_disj a by auto 
    moreover have "a ` J \<subseteq> F"
      using a by auto
    ultimately show "finite J"
      using finite_F Finite_Set.inj_on_finite by blast
  qed
  have JI[simp]: "J \<subseteq> I"
    unfolding J_def by simp
  have "F = (\<Union>i\<in>J. F\<inter>S' i)"
    unfolding J_def apply auto
    by (metis FT T_S' UN_E disjoint_iff_not_equal subsetD)
  hence "(\<Sum>x\<in>F. norm (f x)) = (\<Sum>x\<in>(\<Union>i\<in>J. F\<inter>S' i). norm (f x))"
    by simp
  also have "\<dots> = (\<Sum>i\<in>J. \<Sum>x\<in>F \<inter> S' i. norm (f x))"
  proof (rule sum.UNION_disjoint)
    show "finite J"
      by simp      
    show "\<forall>i\<in>J. finite (F \<inter> S' i)"
      by (simp add: finite_F)      
    show "\<forall>i\<in>J. \<forall>j\<in>J. i \<noteq> j \<longrightarrow> F \<inter> S' i \<inter> (F \<inter> S' j) = {}"
      using S'_disj by auto      
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>J. B i)"
    using sum_FS'_B
    by (simp add: ordered_comm_monoid_add_class.sum_mono)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>J. B i)"
    by simp
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
  proof (rule infsetsum_mono_neutral_left)
    show "B abs_summable_on J"
      by simp      
    show "B abs_summable_on I"
      by simp
    show "B x \<le> B x"
      if "x \<in> J"
      for x :: 'a
      using that
      by simp 
    show "J \<subseteq> I"
      by simp      
    show "0 \<le> B x"
      if "x \<in> I - J"
      for x :: 'a
      using that
      by simp 
  qed    
  finally show "(\<Sum>x\<in>F. norm(f x)) \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
    by simp
qed

lemma abs_summable_product':
  fixes X :: "'a set" and Y :: "'b set"
  assumes "\<And>x. (\<lambda>y. f (x,y)) abs_summable_on Y"
    and "(\<lambda>x. \<Sum>\<^sub>ay\<in>Y. norm (f (x,y))) abs_summable_on X"
  shows "f abs_summable_on X\<times>Y"
proof-
  define S where "S x = {x} \<times> Y" for x :: 'a
  have bij[simp]: "bij_betw (Pair x) Y (S x)" for x
  proof (rule bij_betwI [where g = snd])
    show "Pair x \<in> Y \<rightarrow> S x"
      by (simp add: S_def)      
    show "snd \<in> S x \<rightarrow> Y"
      using Pi_I' S_def by auto      
    show "snd (y, x::'b) = x"
      if "x \<in> Y"
      for x :: 'b and y::'a
      using that
      by simp 
    show "(x, snd y::'b) = y"
      if "y \<in> S x"
      for y :: "'a \<times> 'b"
      using that
      unfolding S_def
      by auto
  qed
  have "f abs_summable_on S x" for x
  proof (subst abs_summable_on_reindex_bij_betw [symmetric , where A = Y and g = "\<lambda>y. (x,y)"])
    show "bij_betw (Pair x) Y (S x)"
      by simp      
    show "(\<lambda>xa. f (x, xa)) abs_summable_on Y"
      using assms(1) by auto      
  qed
  moreover have "bij_betw (Pair x) Y (S x)"
    for x
    unfolding S_def using bij_betw_def
    using S_def bij by auto
  hence "(\<Sum>\<^sub>ay\<in>Y. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>S x. norm (f y))" for x
    by (rule infsetsum_reindex_bij_betw) 
  hence "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    using assms(2) by simp
  hence "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    by auto
  moreover have "X \<times> Y \<subseteq> (\<Union>i\<in>X. S i)"
    unfolding S_def by auto
  ultimately show ?thesis
    by (rule abs_summable_partition[where S=S and I=X])
qed

lemma infsetsum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field,banach,second_countable_topology}"
  assumes finite: "finite A"
    and summable: "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
proof-
  define B' where "B' x = {y\<in>B x. 0 \<noteq> f x y}" for x
  have [simp]: "B' x \<subseteq> B x" for x
    unfolding B'_def by simp
  have PiE_subset: "Pi\<^sub>E A B' \<subseteq> Pi\<^sub>E A B"
    by (simp add: PiE_mono)
  have "f x abs_summable_on B x"
    if "x\<in>A"
    for x
    using that
    by (simp add: local.summable) 
  hence countable: "countable (B' x)" if "x\<in>A" for x
    unfolding B'_def using abs_summable_countable
    using that by blast
  have summable: "f x abs_summable_on B' x" if "x\<in>A" for x
    using that summable[where x = x] \<open>\<And>x. B' x \<subseteq> B x\<close> abs_summable_on_subset by blast
  have 0: "(\<Prod>x\<in>A. f x (g x)) = 0" if "g \<in> Pi\<^sub>E A B - Pi\<^sub>E A B'" for g
  proof-
    from that have "g \<in> extensional A"
      by (simp add: PiE_def)
    from that have "g \<notin> Pi\<^sub>E A B'"
      by simp
    with \<open>g \<in> extensional A\<close> have "g \<notin> Pi A B'"
      unfolding PiE_def by simp
    then obtain x where "x\<in>A" and "g x \<notin> B' x"
      unfolding Pi_def by auto
    hence "f x (g x) = 0"
      unfolding B'_def using that by auto
    with finite show ?thesis
    proof (rule_tac prod_zero)
      show "finite A"
        if "finite A"
          and "f x (g x) = 0"
        using that
        by simp 
      show "\<exists>a\<in>A. f a (g a) = 0"
        if "finite A"
          and "f x (g x) = 0"
        using that \<open>x \<in> A\<close> by blast 
    qed      
  qed

  have d: "infsetsum (f x) (B' x) = infsetsum (f x) (B x)"
    if "x \<in> A"
    for x
  proof (rule infsetsum_cong_neutral)
    show "f y x = 0"
      if "x \<in> B' y - B y"
      for x :: 'b and y :: 'a
      using that
      by (meson DiffD1 DiffD2 \<open>\<And>x. B' x \<subseteq> B x\<close> in_mono) 
    show "f y x = 0"
      if "x \<in> B y - B' y"
      for x :: 'b and y
      using that B'_def by auto 
    show "f y x = f y x"
      if "x \<in> B' y \<inter> B y"
      for x :: 'b and y
      using that
      by simp 
  qed    
  have "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B)
      = infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B')"
  proof (rule infsetsum_cong_neutral)
    show "(\<Prod>a\<in>A. f a (x a)) = 0"
      if "x \<in> Pi\<^sub>E A B - Pi\<^sub>E A B'"
      for x :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: "0") 
    show "(\<Prod>a\<in>A. f a (x a)) = 0"
      if "x \<in> Pi\<^sub>E A B' - Pi\<^sub>E A B"
      for x :: "'a \<Rightarrow> 'b"
      using that PiE_subset by auto 
    show "(\<Prod>a\<in>A. f a (x a)) = (\<Prod>a\<in>A. f a (x a))"
      if "x \<in> Pi\<^sub>E A B \<inter> Pi\<^sub>E A B'"
      for x :: "'a \<Rightarrow> 'b"
      using that
      by simp 
  qed
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B' x))"
    using finite countable summable by (rule infsetsum_prod_PiE)
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
    using d
    by auto
  finally show ?thesis.
qed


lemma infsetsum_0D:
  fixes f :: "'a \<Rightarrow> real"
  assumes "infsetsum f A = 0"
    and abs_sum: "f abs_summable_on A"
    and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    and "x \<in> A"
  shows "f x = 0"
proof -
  from abs_sum have [simp]: "f abs_summable_on (A-{x})"
    by (meson Diff_subset abs_summable_on_subset)
  from abs_sum \<open>x\<in>A\<close> have [simp]: "f abs_summable_on {x}"
    by auto
  have a: "\<And>a. a \<in> A - {x} \<Longrightarrow> a \<in> A"
    by simp   
  from assms have "0 = infsetsum f A"
    by simp
  also have "\<dots> = infsetsum f (A-{x}) + infsetsum f {x}"
  proof (subst infsetsum_Un_disjoint [symmetric])
    show "f abs_summable_on A - {x}"
      by simp      
    show "f abs_summable_on {x}"
      by simp      
    show "(A - {x}) \<inter> {x} = {}"
      by simp      
    show "infsetsum f A = infsetsum f (A - {x} \<union> {x})"
      using assms(4) insert_Diff by fastforce      
  qed
  also have "\<dots> \<ge> 0 + infsetsum f {x}" (is "_ \<ge> \<dots>")
    using a
    by (smt infsetsum_nonneg nneg)    
  also have "\<dots> = f x"
    by simp
  finally have "f x \<le> 0".
  with nneg[OF \<open>x\<in>A\<close>] show "f x = 0"
    by auto
qed

lemma sum_leq_infsetsum:
  fixes f :: "_ \<Rightarrow> real"
  assumes "f abs_summable_on N"
    and "finite M"
    and "M \<subseteq> N"
    and "\<And>x. x\<in>N-M \<Longrightarrow> f x \<ge> 0"
  shows "sum f M \<le> infsetsum f N"
proof -
  have "infsetsum f M \<le> infsetsum f N"
  proof (rule infsetsum_mono_neutral_left)
    show "f abs_summable_on M"
      by (simp add: assms(2))      
    show "f abs_summable_on N"
      by (simp add: assms(1))      
    show "f x \<le> f x"
      if "x \<in> M"
      for x :: 'b
      using that
      by simp 
    show "M \<subseteq> N"
      by (simp add: assms(3))      
    show "0 \<le> f x"
      if "x \<in> N - M"
      for x :: 'b
      using that
      by (simp add: assms(4)) 
  qed
  thus ?thesis
    using assms by auto
qed

lemma infsetsum_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology, division_ring}"
  shows  "infsetsum (\<lambda>x. f x * c) A = infsetsum f A * c"
proof (cases "c \<noteq> 0 \<longrightarrow> f abs_summable_on A")
  case True
  have "(\<Sum>\<^sub>ax\<in>A. f x * c) = infsetsum f A * c"
    if "f abs_summable_on A"
    using infsetsum_cmult_left that by blast
  thus ?thesis
    using True by auto     
next
  case False
  hence "c\<noteq>0" and "\<not> f abs_summable_on A"
    by auto
  have "\<not> (\<lambda>x. f x * c) abs_summable_on A"
  proof (rule notI)
    assume "(\<lambda>x. f x * c) abs_summable_on A"
    hence "(\<lambda>x. (f x * c) * inverse c) abs_summable_on A"
      by (rule abs_summable_on_cmult_left)
    with \<open>\<not> f abs_summable_on A\<close> show False
      by (metis (no_types, lifting) False Groups.mult_ac(1) abs_summable_on_cong mult_1_right
          right_inverse)
  qed
  with \<open>\<not> f abs_summable_on A\<close>
  show ?thesis 
    by (simp add: not_summable_infsetsum_eq)
qed

lemma abs_summable_on_zero_diff:
  assumes "f abs_summable_on A"
    and "\<And>x. x \<in> B - A \<Longrightarrow> f x = 0"
  shows "f abs_summable_on B"
proof (subst asm_rl [of "B = (B-A) \<union> (A\<inter>B)"])
  show "B = B - A \<union> A \<inter> B"
    by auto
  have "(\<lambda>x. 0::real) abs_summable_on B - A"
    by simp    
  moreover have "norm (f x) \<le> 0"
    if "x \<in> B - A"
    for x :: 'a
    using that
    by (simp add: assms(2)) 
  ultimately have "f abs_summable_on B - A"
    by (rule abs_summable_on_comparison_test' [where g = "\<lambda>x. 0"])   
  moreover have "f abs_summable_on A \<inter> B"
    using abs_summable_on_subset assms(1) by blast
  ultimately show "f abs_summable_on B - A \<union> A \<inter> B"
    by (rule abs_summable_on_union)    
qed

lemma abs_summable_on_Sigma_iff:
  "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"
proof auto
  assume sum_AB: "f abs_summable_on Sigma A B"
  define S' where "S' = {x\<in>Sigma A B. 0 \<noteq> f x}"
  from sum_AB have "countable S'"
    unfolding S'_def by (rule abs_summable_countable)
  define A' B' where "A' = fst ` S'" and "B' x = B x \<inter> snd ` S'" for x
  have A'A: \<open>A' \<subseteq> A\<close> and B'B: \<open>B' x \<subseteq> B x\<close> for x
    unfolding A'_def B'_def S'_def by auto
  have  cntA: "countable A'" and cntB: "countable (B' x)" for x
    unfolding A'_def B'_def using \<open>countable S'\<close> by auto
  have f0: "f (x,y) = 0" if "x \<in> A - A'" and "y \<in> B x" for x y
  proof -
    from that have "(x,y) \<in> Sigma A B"
      by auto
    moreover from that have "(x,y) \<notin> S'"
      unfolding A'_def
      by (metis image_eqI mem_simps(6) prod.sel(1)) 
    ultimately show "f (x,y) = 0"
      unfolding S'_def by auto
  qed
  have f0': "f (x,y) = 0" if "x \<in> A" and "y \<in> B x - B' x" for x y
  proof -
    from that have "(x,y) \<in> Sigma A B"
      by auto
    moreover from that have "(x,y) \<notin> S'"
      unfolding B'_def
      by (auto simp add: rev_image_eqI)
    ultimately show "f (x,y) = 0"
      unfolding S'_def by auto
  qed
  have "Sigma A' B' \<subseteq> Sigma A B"
    using A'A B'B by (rule Sigma_mono)
  hence sum_A'B': "f abs_summable_on Sigma A' B'"
    using sum_AB abs_summable_on_subset by auto 
  from sum_A'B' have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A'" for x
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f] that by auto
  moreover have "(\<lambda>y. f (x, y)) abs_summable_on B' x" 
    if t:"x \<in> A - A'" 
    for x
  proof (subst abs_summable_on_zero_diff [where A = "{}"])
    show "(\<lambda>y. f (x, y)) abs_summable_on {}"
      by simp
    have "f (x, a) = 0"
      if "a \<in> B' x"
      for a
      using t f0 that B'B
      by auto
    thus "f (x, a) = 0"
      if "a \<in> B' x - {}"
      for a
      using that by auto 
    show True by blast
  qed     
  ultimately have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A" for x
    using that by auto
  thus "(\<lambda>y. f (x, y)) abs_summable_on B x" if "x \<in> A" for x
    apply (rule abs_summable_on_zero_diff)
    using that f0' by auto

  have Q: "\<And>x. x \<in> A - A' \<Longrightarrow> (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) = 0"
    apply (subst infsetsum_cong[where g=\<open>\<lambda>x. 0\<close> and B="B' _"])
    using f0 B'B by auto

  from sum_A'B' have "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A'"
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f] by auto
  hence "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A"
    apply (rule abs_summable_on_zero_diff)
    using Q by auto
  have R: "\<And>x. x \<in> A \<Longrightarrow>
         (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) =
         (\<Sum>\<^sub>ay\<in>B x. norm (f (x, y)))"
  proof (rule infsetsum_cong_neutral)
    show "norm (f (x, a)) = 0"
      if "x \<in> A"
        and "a \<in> B' x - B x"
      for x :: 'a
        and a :: 'b
      using that B'B by blast 
    show "norm (f (x, a)) = 0"
      if "x \<in> A"
        and "a \<in> B x - B' x"
      for x :: 'a
        and a :: 'b
      using that
      by (simp add: f0') 
    show "norm (f (x, a)) = norm (f (x, a))"
      if "x \<in> A"
        and "a \<in> B' x \<inter> B x"
      for x :: 'a
        and a :: 'b
      using that
      by simp 
  qed
  thus "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A"    
    using \<open>(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A\<close> by auto 
next
  assume sum_B: "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
  assume sum_A: "(\<lambda>x. \<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) abs_summable_on A"
  define B' where "B' x = {y\<in>B x. 0 \<noteq> f (x,y)}" for x
  from sum_B have cnt_B': "countable (B' x)" if "x\<in>A" for x
    unfolding B'_def apply (rule_tac abs_summable_countable)
    using that by auto
  define A' where "A' = {x\<in>A. 0 \<noteq> (\<Sum>\<^sub>ay\<in>B x. norm (f (x, y)))}"
  from sum_A have cnt_A': "countable A'"
    unfolding A'_def by (rule abs_summable_countable)
  have A'A: "A' \<subseteq> A" and B'B: "B' x \<subseteq> B x" for x
    unfolding A'_def B'_def by auto
  have f0': "f (x,y) = 0" if "y \<in> B x - B' x" for x y
    using that unfolding B'_def by auto
  have f0: "f (x,y) = 0" if "x \<in> A - A'" and "y \<in> B x" for x y
  proof -
    have "(\<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) = 0"
      using that unfolding A'_def by auto
    hence "norm (f (x, y)) = 0"
      apply (rule infsetsum_0D)
      using sum_B that by auto
    thus ?thesis
      by auto
  qed

  from sum_B have sum_B': "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x\<in>A" for x
  proof (rule_tac abs_summable_on_subset [where B = "B x"])
    show "(\<lambda>y. f (x, y)) abs_summable_on B x"
      if "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
      using that \<open>x \<in> A\<close> by blast 
    show "B' x \<subseteq> B x"
      if "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
      using that
      by (simp add: B'B) 
  qed
  have *: "(\<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y)))" if "x\<in>A" for x
    using infsetsum_cong_neutral f0' B'B that
    by (metis (no_types, lifting) DiffD1 DiffD2 Int_iff inf.absorb_iff2 norm_zero)
  have "(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A"
    using abs_summable_on_cong sum_A "*" by auto
  hence sum_A': "(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A'"
    using _ A'A abs_summable_on_subset by blast 
  from sum_A' sum_B'
  have "f abs_summable_on Sigma A' B'"
    using abs_summable_on_Sigma_iff[where A=A' and B=B' and f=f, OF cnt_A' cnt_B'] A'A by auto
  moreover have "f x = 0"
    if "x \<in> Sigma A B - Sigma A' B'" for x
    using that f0 f0' by force     
  ultimately show "f abs_summable_on Sigma A B"
    by (rule abs_summable_on_zero_diff)
qed

lemma
  fixes f :: "'a \<Rightarrow> 'c :: {banach, real_normed_field, second_countable_topology}"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  shows   abs_summable_on_product: "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    and   infsetsum_product: "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) =
                                infsetsum f A * infsetsum g B"
proof -
  from assms show "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    by (subst abs_summable_on_Sigma_iff)
      (auto simp: norm_mult infsetsum_cmult_right)
  with assms show "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) = infsetsum f A * infsetsum g B"
    by (subst infsetsum_Sigma)
      (auto simp: infsetsum_cmult_left infsetsum_cmult_right)
qed



lemma infsetsum'_converges_ennreal: \<open>infsetsum'_converges (f::_ \<Rightarrow> ennreal) S\<close>
proof -
  define B where \<open>B = (SUP F\<in>{F. F \<subseteq> S \<and> finite F}. sum f F)\<close>

  have upper: \<open>\<forall>\<^sub>F F in finite_subsets_at_top S. sum f F \<le> B\<close>
    apply (rule eventually_finite_subsets_at_top_weakI)
    unfolding B_def
    by (simp add: SUP_upper)
  have lower: \<open>\<forall>\<^sub>F n in finite_subsets_at_top S. x < sum f n\<close> if \<open>x < B\<close> for x
  proof -
    obtain F where Fx: \<open>sum f F > x\<close> and \<open>F \<subseteq> S\<close> and \<open>finite F\<close>
      using \<open>x < B\<close> unfolding B_def
      by (metis (mono_tags, lifting)  less_SUP_iff mem_Collect_eq)
    have geq: \<open>sum f Y \<ge> sum f F\<close> if \<open>finite Y\<close> and \<open>Y \<supseteq> F\<close> for Y
      by (simp add: sum_mono2 that(1) that(2))
    show ?thesis
      unfolding eventually_finite_subsets_at_top
      apply (rule exI[of _ F])
      using \<open>finite F\<close> \<open>F \<subseteq> S\<close> Fx geq by force
  qed

  show ?thesis
    unfolding infsetsum'_converges_def
    apply (rule exI[of _ B])
    using upper lower by (rule increasing_tendsto)
qed

lemma infsetsum'_superconst_infinite:
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infsetsum' f S = (\<infinity>::ennreal)"
proof -
  have \<open>(sum f \<longlongrightarrow> \<infinity>) (finite_subsets_at_top S)\<close>
  proof (rule order_tendstoI[rotated], simp)
    fix y :: ennreal assume \<open>y < \<infinity>\<close>
    then have \<open>y / b < \<infinity>\<close>
      by (metis b ennreal_divide_eq_top_iff gr_implies_not_zero infinity_ennreal_def top.not_eq_extremum)
    then obtain F where \<open>finite F\<close> and \<open>F \<subseteq> S\<close> and cardF: \<open>card F > y / b\<close>
      using \<open>infinite S\<close>
      by (metis ennreal_Ex_less_of_nat infinite_arbitrarily_large infinity_ennreal_def)
    moreover have \<open>sum f Y > y\<close> if \<open>finite Y\<close> and \<open>F \<subseteq> Y\<close> and \<open>Y \<subseteq> S\<close> for Y
    proof -
      have \<open>y < b * card F\<close>
        by (metis \<open>y < \<infinity>\<close> b cardF divide_less_ennreal ennreal_mult_eq_top_iff gr_implies_not_zero infinity_ennreal_def mult.commute top.not_eq_extremum)
      also have \<open>\<dots> \<le> b * card Y\<close>
        by (meson b card_mono less_imp_le mult_left_mono of_nat_le_iff that(1) that(2))
      also have \<open>\<dots> = sum (\<lambda>_. b) Y\<close>
        by (simp add: mult.commute)
      also have \<open>\<dots> \<le> sum f Y\<close>
        using geqb by (meson subset_eq sum_mono that(3))
      finally show ?thesis
        by -
    qed
    ultimately show \<open>\<forall>\<^sub>F x in finite_subsets_at_top S. y < sum f x\<close>
      unfolding eventually_finite_subsets_at_top 
      by auto
  qed
  then show ?thesis
    unfolding infsetsum'_def 
    apply (simp add: infsetsum'_converges_ennreal)
    by (simp add: tendsto_Lim)
qed

lemma infsetsum'_tendsto:
  assumes \<open>infsetsum'_converges f S\<close>
  shows \<open>((\<lambda>F. sum f F) \<longlongrightarrow> infsetsum' f S) (finite_subsets_at_top S)\<close>
  by (metis assms finite_subsets_at_top_neq_bot infsetsum'_converges_def infsetsum'_def tendsto_Lim)

lemma infsetsum'_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>infsetsum' (\<lambda>_. c) F = of_nat (card F) * c\<close>
  apply (subst infsetsum'_finite[OF assms])
  by simp

lemma infsetsum'_zero[simp]:
  shows \<open>infsetsum' (\<lambda>_. 0) S = 0\<close>
  unfolding infsetsum'_def sum.neutral_const
  by (simp add: tendsto_Lim)

lemma
  fixes f g :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes \<open>infsetsum'_converges f A\<close>
  assumes \<open>infsetsum'_converges g A\<close>
  shows infsetsum'_add: \<open>infsetsum' (\<lambda>x. f x + g x) A = infsetsum' f A + infsetsum' g A\<close>
    and infsetsum'_converges_add: \<open>infsetsum'_converges (\<lambda>x. f x + g x) A\<close>
proof -
  note lim_f = infsetsum'_tendsto[OF assms(1)]
    and lim_g = infsetsum'_tendsto[OF assms(2)]
  then have lim: \<open>(sum (\<lambda>x. f x + g x) \<longlongrightarrow> infsetsum' f A + infsetsum' g A) (finite_subsets_at_top A)\<close>
    unfolding sum.distrib
    by (rule tendsto_add)
  then show conv: \<open>infsetsum'_converges (\<lambda>x. f x + g x) A\<close>
    unfolding infsetsum'_converges_def by auto
  show \<open>infsetsum' (\<lambda>x. f x + g x) A = infsetsum' f A + infsetsum' g A\<close>
    unfolding infsetsum'_def 
    using lim_f lim_g lim
    by (auto simp: assms conv tendsto_Lim)
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes "infsetsum'_converges f A"
  assumes "infsetsum'_converges f B"
  assumes disj: "A \<inter> B = {}"
  shows infsetsum'_Un_disjoint: \<open>infsetsum' f (A \<union> B) = infsetsum' f A + infsetsum' f B\<close>
    and infsetsum'_converges_Un_disjoint: \<open>infsetsum'_converges f (A \<union> B)\<close>
proof -
  define fA fB where \<open>fA x = (if x \<in> A then f x else 0)\<close>
    and \<open>fB x = (if x \<notin> A then f x else 0)\<close> for x
  have conv_fA: \<open>infsetsum'_converges fA (A \<union> B)\<close>
    unfolding fA_def
    apply (subst infsetsum'_converges_subset_zero, auto)
    by (simp add: assms(1) infsetsum'_converges_cong)
  have conv_fB: \<open>infsetsum'_converges fB (A \<union> B)\<close>
    unfolding fB_def
    apply (subst infsetsum'_converges_subset_zero, auto)
    by (smt (verit, ccfv_SIG) assms(2) assms(3) disjoint_iff infsetsum'_converges_cong)
  have fAB: \<open>f x = fA x + fB x\<close> for x
    unfolding fA_def fB_def by simp
  have \<open>infsetsum' f (A \<union> B) = infsetsum' fA (A \<union> B) + infsetsum' fB (A \<union> B)\<close>
    unfolding fAB
    using conv_fA conv_fB by (rule infsetsum'_add)
  also have \<open>\<dots> = infsetsum' fA A + infsetsum' fB B\<close>
    unfolding fA_def fB_def
    by (subst infsetsum'_subset_zero[where A=\<open>A\<union>B\<close>], auto)+
  also have \<open>\<dots> = infsetsum' f A + infsetsum' f B\<close>
    apply (subst infsetsum'_cong[where f=fA and g=f], simp add: fA_def)
    apply (subst infsetsum'_cong[where f=fB and g=f], simp add: fB_def)
    using disj by auto
  finally show \<open>infsetsum' f (A \<union> B) = infsetsum' f A + infsetsum' f B\<close>
    by -
  from conv_fA conv_fB
  have \<open>infsetsum'_converges (\<lambda>x. fA x + fB x) (A \<union> B)\<close>
    by (rule infsetsum'_converges_add)
  then show \<open>infsetsum'_converges f (A \<union> B)\<close>
    unfolding fAB by -
qed

lemma infsetsum'_converges_union_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> infsetsum'_converges f (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>infsetsum'_converges f (\<Union>a\<in>A. B a)\<close>
  using finite conv disj apply induction by (auto intro!: infsetsum'_converges_Un_disjoint)

lemma sum_infsetsum':
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> infsetsum'_converges f (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>sum (\<lambda>a. infsetsum' f (B a)) A = infsetsum' f (\<Union>a\<in>A. B a)\<close>
  using assms
proof (insert finite conv disj, induction)
  case empty
  then show ?case 
    by simp
next
  case (insert x F)
  have \<open>(\<Sum>a\<in>insert x F. infsetsum' f (B a)) = infsetsum' f (B x) + (\<Sum>a\<in>F. infsetsum' f (B a))\<close>
    apply (subst sum.insert) using insert by auto
  also have \<open>\<dots> = infsetsum' f (B x) + infsetsum' f (\<Union> (B ` F))\<close>
    apply (subst insert.IH) using assms insert by auto
  also have \<open>\<dots> = infsetsum' f (B x \<union> \<Union> (B ` F))\<close>
    apply (rule infsetsum'_Un_disjoint[symmetric])
    using insert.prems insert.hyps by (auto simp: infsetsum'_converges_union_disjoint)
  also have \<open>\<dots> = infsetsum' f (\<Union>a\<in>insert x F. B a)\<close>
    by auto
  finally show ?case
    by -
qed

theorem infsetsum'_mono:
  fixes f g :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "infsetsum'_converges f A"
    and "infsetsum'_converges g A"
  assumes leq: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "infsetsum' f A \<le> infsetsum' g A"
proof -
  note limf = infsetsum'_tendsto[OF assms(1)]
    and limg =  infsetsum'_tendsto[OF assms(2)]
  have sum_leq: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> sum g F\<close>
    by (simp add: in_mono leq sum_mono)
  show ?thesis
    using _ limg limf apply (rule tendsto_le)
    by (auto intro!: sum_leq)
qed

end
