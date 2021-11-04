section \<open>\<open>Complex_L2\<close> -- Hilbert space of square-summable functions\<close>

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Complex_L2
  imports 
    Complex_Bounded_Linear_Function

    "HOL-Analysis.L2_Norm"
    "HOL-Library.Rewrite"
    "HOL-Analysis.Infinite_Set_Sum"
    "Complex_Bounded_Operators.Extra_Infinite_Set_Sum"
begin

unbundle cblinfun_notation
unbundle no_notation_blinfun_apply

subsection \<open>l2 norm of functions\<close>

definition "has_ell2_norm x = bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"

lemma has_ell2_norm_infsetsum: "has_ell2_norm x \<longleftrightarrow> (\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
proof
  define f where "f i = (cmod (x i))\<^sup>2" for i
  assume fsums: "f abs_summable_on UNIV"
  define bound where "bound = infsetsum f UNIV"
  have "sum f F \<le> bound" if "finite F" for F
  proof -
    have "sum f F = infsetsum f F"
      using that by (rule infsetsum_finite[symmetric])
    also have "infsetsum f F \<le> infsetsum f UNIV"
    proof (rule infsetsum_mono_neutral_left)
      show "f abs_summable_on F"
        by (simp add: that)        
      show "f abs_summable_on UNIV"
        by (simp add: fsums)      
      show "f x \<le> f x"
        if "x \<in> F"
        for x :: 'a
        using that
        by simp 
      show "F \<subseteq> UNIV"
        by simp        
      show "0 \<le> f x"
        if "x \<in> UNIV - F"
        for x :: 'a
        using that f_def by auto
    qed
    finally show ?thesis 
      unfolding bound_def by assumption
  qed
  thus "has_ell2_norm x"
    unfolding has_ell2_norm_def f_def
    by (rule bdd_aboveI2[where M=bound], simp)
next
  have x1: "\<exists>B. \<forall>F. finite F \<longrightarrow> (\<Sum>s\<in>F. (cmod (x s))\<^sup>2) < B"
    if "\<And>t. finite t \<Longrightarrow> (\<Sum>i\<in>t. (cmod (x i))\<^sup>2) \<le> M"
    for M
    using that by (meson gt_ex le_less_trans)
  assume "has_ell2_norm x"
  then obtain B where "(\<Sum>xa\<in>F. norm ((cmod (x xa))\<^sup>2)) < B" if "finite F" for F
  proof atomize_elim    
    show "\<exists>B. \<forall>F. finite F \<longrightarrow> (\<Sum>xa\<in>F. norm ((cmod (x xa))\<^sup>2)) < B"
      if "has_ell2_norm x"
      using that x1
      unfolding has_ell2_norm_def unfolding bdd_above_def
      by auto
  qed 
  thus "(\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
  proof (rule_tac abs_summable_finiteI [where B = B])
    show "(\<Sum>t\<in>F. norm ((cmod (x t))\<^sup>2)) \<le> B"
      if "\<And>F. finite F \<Longrightarrow> (\<Sum>s\<in>F. norm ((cmod (x s))\<^sup>2)) < B"
        and "finite F" and "F \<subseteq> UNIV"
      for F :: "'a set"
      using that by fastforce
  qed     
qed

lemma has_ell2_norm_L2_set: "has_ell2_norm x = bdd_above (L2_set (norm o x) ` Collect finite)"
proof-
  have bdd_above_image_mono': "bdd_above (f`A)"
    if "\<And>x y. x\<le>y \<Longrightarrow> x:A \<Longrightarrow> y:A \<Longrightarrow> f x \<le> f y"
      and "\<exists>M\<in>A. \<forall>x \<in> A. x \<le> M"
    for f::"'a set\<Rightarrow>real" and A
    using that
    unfolding bdd_above_def by auto
  have t3: "bdd_above X \<Longrightarrow> bdd_above (sqrt ` X)" for X
    by (meson bdd_aboveI2 bdd_above_def real_sqrt_le_iff)
  moreover have t2: "bdd_above X" if bdd_sqrt: "bdd_above (sqrt ` X)" for X
  proof-
    obtain y where y:"y \<ge> sqrt x" if "x:X" for x 
      using bdd_sqrt unfolding bdd_above_def by auto
    have "y*y \<ge> x" if "x:X" for x
      by (metis power2_eq_square sqrt_le_D that y)
    thus "bdd_above X"
      unfolding bdd_above_def by auto
  qed
  ultimately have bdd_sqrt: "bdd_above X \<longleftrightarrow> bdd_above (sqrt ` X)" for X
    by rule
  have t1: "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) =
            bdd_above ((\<lambda>A. sqrt (\<Sum>i\<in>A. ((cmod \<circ> x) i)\<^sup>2)) ` Collect finite)"
  proof (rewrite asm_rl [of "(\<lambda>A. sqrt (sum (\<lambda>i. ((cmod \<circ> x) i)\<^sup>2) A)) ` Collect finite 
                            = sqrt ` (\<lambda>A. (\<Sum>i\<in>A. (cmod (x i))\<^sup>2)) ` Collect finite"])
    show "(\<lambda>A. sqrt (\<Sum>i\<in>A. ((cmod \<circ> x) i)\<^sup>2)) ` Collect finite = sqrt ` sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite"
      by auto      
    show "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) = bdd_above (sqrt ` sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
      by (meson t2 t3)      
  qed
  show "has_ell2_norm x \<longleftrightarrow> bdd_above (L2_set (norm o x) ` Collect finite)"
    unfolding has_ell2_norm_def L2_set_def
    using t1.
qed

definition "ell2_norm x = sqrt (SUP F\<in>{F. finite F}. sum (\<lambda>i. norm (x i)^2) F)" for x :: \<open>'a \<Rightarrow> complex\<close>

lemma ell2_norm_L2_set: 
  assumes "has_ell2_norm x"
  shows "ell2_norm x = (SUP F\<in>{F. finite F}. L2_set (norm o x) F)"
proof-
  have "sqrt (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)) =
      (SUP F\<in>{F. finite F}. sqrt (\<Sum>i\<in>F. (cmod (x i))\<^sup>2))"
  proof (subst continuous_at_Sup_mono)
    show "mono sqrt"
      by (simp add: mono_def)      
    show "continuous (at_left (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite))) sqrt"
      using continuous_at_split isCont_real_sqrt by blast    
    show "sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite \<noteq> {}"
      by auto      
    show "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
      by (metis assms has_ell2_norm_def)      
    show "\<Squnion> (sqrt ` sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) = (SUP F\<in>Collect finite. sqrt (\<Sum>i\<in>F. (cmod (x i))\<^sup>2))"
      by (metis image_image)      
  qed  
  thus ?thesis 
    unfolding ell2_norm_def L2_set_def o_def.
qed

lemma ell2_norm_infsetsum:
  assumes "has_ell2_norm x"
  shows "ell2_norm x = sqrt (infsetsum (\<lambda>i. (norm(x i))^2) UNIV)"
proof-
  have "ell2_norm x = sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2)"
  proof (subst infsetsum_nonneg_is_SUPREMUM)
    show "(\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
      using assms has_ell2_norm_infsetsum by fastforce      
    show "0 \<le> (cmod (x t))\<^sup>2"
      if "t \<in> UNIV"
      for t :: 'a
      using that
      by simp 
    show "ell2_norm x = sqrt (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` {F. finite F \<and> F \<subseteq> UNIV}))"
      unfolding ell2_norm_def by auto   
  qed
  thus ?thesis 
    by auto
qed

lemma has_ell2_norm_finite[simp]: "has_ell2_norm (x::'a::finite\<Rightarrow>_)"
  unfolding has_ell2_norm_def by simp

lemma ell2_norm_finite: 
  "ell2_norm (x::'a::finite\<Rightarrow>complex) = sqrt (sum (\<lambda>i. (norm(x i))^2) UNIV)"
proof-    
  have "(\<Sum>i\<in>t. (cmod (x i))\<^sup>2) \<le> (\<Sum>i\<in>y. (cmod (x i))\<^sup>2)"
    if "t \<subseteq> y"
    for t y
  proof (subst sum_mono2)
    show "finite y"
      by simp      
    show "t \<subseteq> y"
      using that.
    show "0 \<le> (cmod (x b))\<^sup>2"
      if "b \<in> y - t"
      for b :: 'a
      using that
      by simp 
    show True by blast
  qed
  hence mono: "mono (sum (\<lambda>i. (cmod (x i))\<^sup>2))"
    unfolding mono_def
    by blast 
  show ?thesis
    unfolding ell2_norm_def apply (subst image_of_maximum[where m=UNIV])
    using mono by auto
qed

lemma ell2_norm_finite_L2_set: "ell2_norm (x::'a::finite\<Rightarrow>complex) = L2_set (norm o x) UNIV"
proof (subst ell2_norm_L2_set)
  show "has_ell2_norm x"
    by simp    
  show "\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite) = L2_set (cmod \<circ> x) UNIV"
  proof (subst image_of_maximum[where m = UNIV])
    show "mono (L2_set (cmod \<circ> x))"
      by (auto simp: mono_def intro!: L2_set_mono2)
    show "(x::'a set) \<subseteq> UNIV"
      if "(x::'a set) \<in> Collect finite"
      for x :: "'a set"
      using that
      by simp 
    show "(UNIV::'a set) \<in> Collect finite"
      by simp      
    show "L2_set (cmod \<circ> x) UNIV = L2_set (cmod \<circ> x) UNIV"
      by simp
  qed
qed 

lemma ell2_ket:
  fixes a
  defines \<open>f \<equiv> (\<lambda>i. if a = i then 1 else 0)\<close>
  shows has_ell2_norm_ket: \<open>has_ell2_norm f\<close>
    and ell2_norm_ket: \<open>ell2_norm f = 1\<close>
proof -
  have finite_bound: \<open>(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1\<close> if \<open>finite F\<close> for F
  proof - 
    have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 0" if "a\<notin>F"
    proof (subst sum.cong [where B = F and h = "\<lambda>_. 0"])
      show "F = F"
        by blast
      show "(cmod (if a = x then 1 else 0))\<^sup>2 = 0"
        if "x \<in> F"
        for x :: 'a
        using that \<open>a \<notin> F\<close> by auto 
      show "(\<Sum>_\<in>F. (0::real)) = 0"
        by simp
    qed 
    moreover have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1" if "a\<in>F"
    proof -
      obtain F0 where "a\<notin>F0" and F_F0: "F=insert a F0"
        by (meson \<open>a \<in> F\<close> mk_disjoint_insert) 
      have "(\<Sum>i\<in>insert a F0. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
      proof (subst sum.insert_remove)
        show "finite F0"
          using F_F0 \<open>finite F\<close> by auto
        show "(cmod (if a = a then 1 else 0))\<^sup>2 + (\<Sum>i\<in>F0 - {a}. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
          using sum.not_neutral_contains_not_neutral by fastforce        
      qed
      thus "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
        unfolding F_F0.
    qed
    ultimately show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
      unfolding f_def by linarith
  qed

  show \<open>has_ell2_norm f\<close>
    using finite_bound
    by (auto intro!: bdd_aboveI[where M=1] simp: f_def has_ell2_norm_def)

  have \<open>(SUP F\<in>{F. finite F}. sum (\<lambda>i. norm (f i)^2) F) = 1\<close>
    using finite_bound 
    by (auto intro!: cSup_eq_maximum rev_image_eqI[where x=\<open>{a}\<close>]
        simp: f_def)
  then show \<open>ell2_norm f = 1\<close>
    unfolding ell2_norm_def by simp
qed

lemma ell2_norm_geq0:
  assumes \<open>has_ell2_norm x\<close>
  shows \<open>ell2_norm x \<ge> 0\<close>
  by (smt (verit, ccfv_SIG) assms cSUP_upper2 ell2_norm_def finite.intros(1) has_ell2_norm_def mem_Collect_eq real_sqrt_abs real_sqrt_le_iff sum.empty zero_power2)

lemma ell2_norm_point_bound:
  assumes \<open>has_ell2_norm x\<close>
  shows \<open>ell2_norm x \<ge> cmod (x i)\<close>
proof -
  have \<open>(cmod (x i))\<^sup>2 = sum (\<lambda>i. (cmod (x i))\<^sup>2) {i}\<close>
    by auto
  also have "\<dots> \<le> (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite))" 
    apply (rule cSUP_upper2[where x=\<open>{i}\<close>])
      apply auto by (metis assms has_ell2_norm_def)
  also have \<open>\<dots> = (ell2_norm x)^2\<close>
    by (smt (verit, best) SUP_cong calculation ell2_norm_def norm_ge_zero norm_power_ineq real_sqrt_pow2 sum.cong)
  finally show ?thesis
    by (simp add: assms ell2_norm_geq0)
qed

lemma ell2_norm_0:
  assumes "has_ell2_norm x"
  shows "(ell2_norm x = 0) = (x = (\<lambda>_. 0))"
proof
  assume u1: "x = (\<lambda>_. 0)"
  have u2: "(SUP x::'a set\<in>Collect finite. (0::real)) = 0"
    if "x = (\<lambda>_. 0)"
    by (metis cSUP_const empty_Collect_eq finite.emptyI)
  show "ell2_norm x = 0"
    unfolding ell2_norm_def
    using u1 u2 by auto 
next
  assume norm0: "ell2_norm x = 0"
  show "x = (\<lambda>_. 0)"
  proof
    fix i
    have \<open>cmod (x i) \<le> ell2_norm x\<close>
      using assms by (rule ell2_norm_point_bound)
    also have \<open>\<dots> = 0\<close>
      by (fact norm0)
    finally show "x i = 0" by auto
  qed
qed


lemma ell2_norm_smult:
  assumes "has_ell2_norm x"
  shows "has_ell2_norm (\<lambda>i. c * x i)" and "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x"
proof -
  have L2_set_mul: "L2_set (cmod \<circ> (\<lambda>i. c * x i)) F = cmod c * L2_set (cmod \<circ> x) F" for F
  proof-
    have "L2_set (cmod \<circ> (\<lambda>i. c * x i)) F = L2_set (\<lambda>i. (cmod c * (cmod o x) i)) F"
      by (metis comp_def norm_mult)
    also have "\<dots> = cmod c * L2_set (cmod o x) F"
      by (metis norm_ge_zero L2_set_right_distrib)
    finally show ?thesis .
  qed

  from assms obtain M where M: "M \<ge> L2_set (cmod o x) F" if "finite F" for F
    unfolding has_ell2_norm_L2_set bdd_above_def by auto
  hence "cmod c * M \<ge> L2_set (cmod o (\<lambda>i. c * x i)) F" if "finite F" for F
    unfolding L2_set_mul
    by (simp add: ordered_comm_semiring_class.comm_mult_left_mono that) 
  thus has: "has_ell2_norm (\<lambda>i. c * x i)"
    unfolding has_ell2_norm_L2_set bdd_above_def using L2_set_mul[symmetric] by auto
  have "ell2_norm (\<lambda>i. c * x i) = (SUP F \<in> Collect finite. (L2_set (cmod \<circ> (\<lambda>i. c * x i)) F))"
    by (simp add: ell2_norm_L2_set has)
  also have "\<dots> = (SUP F \<in> Collect finite. (cmod c * L2_set (cmod \<circ> x) F))"
    using L2_set_mul by auto   
  also have "\<dots> = cmod c * ell2_norm x" 
  proof (subst ell2_norm_L2_set)
    show "has_ell2_norm x"
      by (simp add: assms)      
    show "(SUP F\<in>Collect finite. cmod c * L2_set (cmod \<circ> x) F) = cmod c * \<Squnion> (L2_set (cmod \<circ> x) ` Collect finite)"
    proof (subst continuous_at_Sup_mono [where f = "\<lambda>x. cmod c * x"])
      show "mono ((*) (cmod c))"
        by (simp add: mono_def ordered_comm_semiring_class.comm_mult_left_mono)
      show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) ((*) (cmod c))"
      proof (rule continuous_mult)
        show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) (\<lambda>x. cmod c)"
          by simp
        show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) (\<lambda>x. x)"
          by simp
      qed    
      show "L2_set (cmod \<circ> x) ` Collect finite \<noteq> {}"
        by auto        
      show "bdd_above (L2_set (cmod \<circ> x) ` Collect finite)"
        by (meson assms has_ell2_norm_L2_set)        
      show "(SUP F\<in>Collect finite. cmod c * L2_set (cmod \<circ> x) F) = \<Squnion> ((*) (cmod c) ` L2_set (cmod \<circ> x) ` Collect finite)"
        by (metis image_image)        
    qed   
  qed     
  finally show "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x".
qed


lemma ell2_norm_triangle:
  assumes "has_ell2_norm x" and "has_ell2_norm y"
  shows "has_ell2_norm (\<lambda>i. x i + y i)" and "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
proof -
  have triangle: "L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F \<le> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" 
    (is "?lhs\<le>?rhs") 
    if "finite F" for F
  proof -
    have "?lhs \<le> L2_set (\<lambda>i. (cmod o x) i + (cmod o y) i) F"
    proof (rule L2_set_mono)
      show "(cmod \<circ> (\<lambda>i. x i + y i)) i \<le> (cmod \<circ> x) i + (cmod \<circ> y) i"
        if "i \<in> F"
        for i :: 'a
        using that norm_triangle_ineq by auto 
      show "0 \<le> (cmod \<circ> (\<lambda>i. x i + y i)) i"
        if "i \<in> F"
        for i :: 'a
        using that
        by simp 
    qed
    also have "\<dots> \<le> ?rhs"
      by (rule L2_set_triangle_ineq)
    finally show ?thesis .
  qed
  obtain Mx My where Mx: "Mx \<ge> L2_set (cmod o x) F" and My: "My \<ge> L2_set (cmod o y) F" 
    if "finite F" for F
    using assms unfolding has_ell2_norm_L2_set bdd_above_def by auto
  hence MxMy: "Mx + My \<ge> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" if "finite F" for F
    using that by fastforce
  hence bdd_plus: "bdd_above ((\<lambda>xa. L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa) ` Collect finite)"
    unfolding bdd_above_def by auto
  from MxMy have MxMy': "Mx + My \<ge> L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F" if "finite F" for F 
    using triangle that by fastforce
  thus has: "has_ell2_norm (\<lambda>i. x i + y i)"
    unfolding has_ell2_norm_L2_set bdd_above_def by auto
  have SUP_plus: "(SUP x\<in>A. f x + g x) \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" 
    if notempty: "A\<noteq>{}" and bddf: "bdd_above (f`A)"and bddg: "bdd_above (g`A)"
    for f g :: "'a set \<Rightarrow> real" and A
  proof-
    have xleq: "x \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" if x: "x \<in> (\<lambda>x. f x + g x) ` A" for x
    proof -
      obtain a where aA: "a:A" and ax: "x = f a + g a"
        using x by blast
      have fa: "f a \<le> (SUP x\<in>A. f x)"
        by (simp add: bddf aA cSUP_upper)
      moreover have "g a \<le> (SUP x\<in>A. g x)"
        by (simp add: bddg aA cSUP_upper)
      ultimately have "f a + g a \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" by simp
      with ax show ?thesis by simp
    qed
    have "(\<lambda>x. f x + g x) ` A \<noteq> {}"
      using notempty by auto        
    moreover have "x \<le> \<Squnion> (f ` A) + \<Squnion> (g ` A)"
      if "x \<in> (\<lambda>x. f x + g x) ` A"
      for x :: real
      using that
      by (simp add: xleq) 
    ultimately show ?thesis
      by (meson bdd_above_def cSup_le_iff)      
  qed
  have a2: "bdd_above (L2_set (cmod \<circ> x) ` Collect finite)"
    by (meson assms(1) has_ell2_norm_L2_set)    
  have a3: "bdd_above (L2_set (cmod \<circ> y) ` Collect finite)"
    by (meson assms(2) has_ell2_norm_L2_set)    
  have a1: "Collect finite \<noteq> {}"
    by auto    
  have a4: "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite)
    \<le> (SUP xa\<in>Collect finite.
           L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa)"
    by (metis (mono_tags, lifting) a1 bdd_plus cSUP_mono mem_Collect_eq triangle)    
  have "\<forall>r. \<Squnion> (L2_set (cmod \<circ> (\<lambda>a. x a + y a)) ` Collect finite) \<le> r \<or> \<not> (SUP A\<in>Collect finite. L2_set (cmod \<circ> x) A + L2_set (cmod \<circ> y) A) \<le> r"
    using a4 by linarith
  hence "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite)
    \<le> \<Squnion> (L2_set (cmod \<circ> x) ` Collect finite) +
       \<Squnion> (L2_set (cmod \<circ> y) ` Collect finite)"
    by (metis (no_types) SUP_plus a1 a2 a3)
  hence "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite) \<le> ell2_norm x + ell2_norm y"
    by (simp add: assms(1) assms(2) ell2_norm_L2_set)
  thus "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
    by (simp add: ell2_norm_L2_set has)  
qed

lemma ell2_norm_uminus:
  assumes "has_ell2_norm x"
  shows \<open>has_ell2_norm (\<lambda>i. - x i)\<close> and \<open>ell2_norm (\<lambda>i. - x i) = ell2_norm x\<close>
  using assms by (auto simp: has_ell2_norm_def ell2_norm_def)

subsection \<open>The type \<open>ell2\<close> of square-summable functions\<close>

typedef 'a ell2 = "{x::'a\<Rightarrow>complex. has_ell2_norm x}"
  unfolding has_ell2_norm_def by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_ell2

instantiation ell2 :: (type)complex_vector begin
lift_definition zero_ell2 :: "'a ell2" is "\<lambda>_. 0" by (auto simp: has_ell2_norm_def)
lift_definition uminus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2" is uminus by (simp add: has_ell2_norm_def)
lift_definition plus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x + g x"
  by (rule ell2_norm_triangle) 
lift_definition minus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x - g x"
  apply (subst add_uminus_conv_diff[symmetric])
  apply (rule ell2_norm_triangle)
  by (auto simp add: ell2_norm_uminus)
lift_definition scaleR_ell2 :: "real \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>r f x. complex_of_real r * f x"
  by (rule ell2_norm_smult)
lift_definition scaleC_ell2 :: "complex \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>c f x. c * f x"
  by (rule ell2_norm_smult)

instance
proof
  fix a b c :: "'a ell2"

  show "((*\<^sub>R) r::'a ell2 \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)" for r
    apply (rule ext) apply transfer by auto
  show "a + b + c = a + (b + c)"
    by (transfer; rule ext; simp)
  show "a + b = b + a"
    by (transfer; rule ext; simp)
  show "0 + a = a"
    by (transfer; rule ext; simp)
  show "- a + a = 0"
    by (transfer; rule ext; simp)
  show "a - b = a + - b"
    by (transfer; rule ext; simp)
  show "r *\<^sub>C (a + b) = r *\<^sub>C a + r *\<^sub>C b" for r
    apply (transfer; rule ext)
    by (simp add: vector_space_over_itself.scale_right_distrib)
  show "(r + r') *\<^sub>C a = r *\<^sub>C a + r' *\<^sub>C a" for r r'
    apply (transfer; rule ext)
    by (simp add: ring_class.ring_distribs(2)) 
  show "r *\<^sub>C r' *\<^sub>C a = (r * r') *\<^sub>C a" for r r'
    by (transfer; rule ext; simp)
  show "1 *\<^sub>C a = a"
    by (transfer; rule ext; simp)
qed
end

instantiation ell2 :: (type)complex_normed_vector begin
lift_definition norm_ell2 :: "'a ell2 \<Rightarrow> real" is ell2_norm .
declare norm_ell2_def[code del]
definition "dist x y = norm (x - y)" for x y::"'a ell2"
definition "sgn x = x /\<^sub>R norm x" for x::"'a ell2"
definition [code del]: "uniformity = (INF e\<in>{0<..}. principal {(x::'a ell2, y). norm (x - y) < e})"
definition [code del]: "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a ell2 set"
instance
proof
  fix a b :: "'a ell2"
  show "dist a b = norm (a - b)"
    by (simp add: dist_ell2_def)    
  show "sgn a = a /\<^sub>R norm a"
    by (simp add: sgn_ell2_def)    
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a ell2) y < e})"
    unfolding dist_ell2_def  uniformity_ell2_def by simp
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a ell2) = x \<longrightarrow> y \<in> U)" for U :: "'a ell2 set"
    unfolding uniformity_ell2_def open_ell2_def by simp_all        
  show "(norm a = 0) = (a = 0)"
    apply transfer by (fact ell2_norm_0)    
  show "norm (a + b) \<le> norm a + norm b"
    apply transfer by (fact ell2_norm_triangle)
  show "norm (r *\<^sub>R (a::'a ell2)) = \<bar>r\<bar> * norm a" for r
    and a :: "'a ell2"
    apply transfer
    by (simp add: ell2_norm_smult(2)) 
  show "norm (r *\<^sub>C a) = cmod r * norm a" for r
    apply transfer
    by (simp add: ell2_norm_smult(2)) 
qed  
end

lemma norm_point_bound_ell2: "norm (Rep_ell2 x i) \<le> norm x"
  apply transfer
  by (simp add: ell2_norm_point_bound)

lemma ell2_norm_finite_support:
  assumes \<open>finite S\<close> \<open>\<And> i. i \<notin> S \<Longrightarrow> Rep_ell2 x i = 0\<close>
  shows \<open>norm x = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S)\<close>
proof -
  have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S \<le> (Sup (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite))\<close>
  proof-
    have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S \<in>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)\<close>
      using \<open>finite S\<close>
      by simp
    moreover have \<open>bdd_above (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)\<close>
      using Rep_ell2 unfolding has_ell2_norm_def
      by auto
    ultimately show ?thesis using cSup_upper by simp
  qed
  moreover have \<open>(Sup (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)) \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
  proof-
    have \<open>t \<in> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite) \<Longrightarrow> t \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
      for t
    proof-
      assume \<open>t \<in> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)\<close>
      hence \<open>\<exists> R \<in> (Collect finite). t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) R\<close> 
        by blast
      then obtain R where \<open>R \<in> (Collect finite)\<close> and \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) R\<close>
        by blast
      from \<open>R \<in> (Collect finite)\<close>
      have \<open>finite R\<close>
        by blast
      have \<open>R = (R - S) \<union> (R \<inter> S)\<close>
        by (simp add: Un_Diff_Int)
      moreover have \<open>(R - S) \<inter> (R \<inter> S) = {}\<close>
        by auto
      ultimately have  \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R - S)
         + (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R \<inter> S)\<close>
        using \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) R\<close> and \<open>finite R\<close>
        by (smt sum.Int_Diff)
      moreover have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R - S) = 0\<close>
      proof-
        have \<open>r \<in> R - S \<Longrightarrow> (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) r = 0\<close>
          for r
          by (simp add: assms(2))        
        thus ?thesis
          by simp 
      qed
      ultimately have \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R \<inter> S)\<close>
        by simp
      moreover have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R \<inter> S) \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
      proof-
        have \<open>R \<inter> S \<subseteq> S\<close>
          by simp        
        moreover have \<open>(\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) i \<ge> 0\<close>
          for i
          by auto        
        ultimately show ?thesis
          by (simp add: assms(1) sum_mono2) 
      qed
      ultimately show \<open>t \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close> by simp
    qed
    moreover have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite) \<noteq> {}\<close>
      by auto      
    ultimately show ?thesis
      by (simp add: cSup_least) 
  qed
  ultimately have \<open>(Sup (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)) = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
    by simp
  thus ?thesis
    by (metis ell2_norm_def norm_ell2.rep_eq) 
qed


instantiation ell2 :: (type) complex_inner begin
lift_definition cinner_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> complex" is 
  "\<lambda>x y. infsetsum (\<lambda>i. (cnj (x i) * y i)) UNIV" .
declare cinner_ell2_def[code del]

instance
proof standard
  fix x y z :: "'a ell2" fix c :: complex
  show "cinner x y = cnj (cinner y x)"
  proof transfer
    fix x y :: "'a\<Rightarrow>complex" assume "has_ell2_norm x" and "has_ell2_norm y"
    have "(\<Sum>\<^sub>ai. cnj (x i) * y i) = (\<Sum>\<^sub>ai. cnj (cnj (y i) * x i))"
      by (metis complex_cnj_cnj complex_cnj_mult mult.commute)
    also have "\<dots> = cnj (\<Sum>\<^sub>ai. cnj (y i) * x i)"
      by (metis infsetsum_cnj) 
    finally show "(\<Sum>\<^sub>ai. cnj (x i) * y i) = cnj (\<Sum>\<^sub>ai. cnj (y i) * x i)" .
  qed

  show "cinner (x + y) z = cinner x z + cinner y z"
  proof transfer
    fix x y z :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm y"
    hence cnj_y: "(\<lambda>i. cnj (y i) * cnj (y i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm z"
    hence z: "(\<lambda>i. z i * z i) abs_summable_on UNIV" 
      by (simp add: norm_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    have cnj_x_z:"(\<lambda>i. cnj (x i) * z i) abs_summable_on UNIV"
      using cnj_x z by (rule abs_summable_product) 
    have cnj_y_z:"(\<lambda>i. cnj (y i) * z i) abs_summable_on UNIV"
      using cnj_y z by (rule abs_summable_product) 
    show "(\<Sum>\<^sub>ai. cnj (x i + y i) * z i) = (\<Sum>\<^sub>ai. cnj (x i) * z i) + (\<Sum>\<^sub>ai. cnj (y i) * z i)"
    proof (subst infsetsum_add [symmetric])
      show "(\<lambda>i. cnj (x i) * z i) abs_summable_on UNIV"
        by (simp add: cnj_x_z)        
      show "(\<lambda>i. cnj (y i) * z i) abs_summable_on UNIV"
        by (simp add: cnj_y_z)        
      show "(\<Sum>\<^sub>ai. cnj (x i + y i) * z i) = (\<Sum>\<^sub>ai. cnj (x i) * z i + cnj (y i) * z i)"
        by (metis complex_cnj_add distrib_right)
    qed
  qed

  show "cinner (c *\<^sub>C x) y = cnj c * cinner x y"
  proof transfer
    fix x y :: "'a \<Rightarrow> complex" and c :: complex
    assume "has_ell2_norm x"
    hence cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm y"
    hence y: "(\<lambda>i. y i * y i) abs_summable_on UNIV" 
      by (simp add: norm_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    have cnj_x_y:"(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
      using cnj_x y by (rule abs_summable_product) 
    thus "(\<Sum>\<^sub>ai. cnj (c * x i) * y i) = cnj c * (\<Sum>\<^sub>ai. cnj (x i) * y i)"
    proof (subst infsetsum_cmult_right [symmetric])
      show "(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
        if "(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
          and "cnj c \<noteq> 0"
        using that
        by simp 
      show "(\<Sum>\<^sub>ai. cnj (c * x i) * y i) = (\<Sum>\<^sub>ai. cnj c * (cnj (x i) * y i))"
        if "(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
        using that
        by (metis complex_cnj_mult vector_space_over_itself.scale_scale) 
    qed
  qed

  show "0 \<le> cinner x x"
  proof transfer
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence "(\<lambda>i. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      by (simp del: abs_summable_on_norm_iff add: norm_mult has_ell2_norm_infsetsum power2_eq_square)
    hence "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      by (subst abs_summable_on_norm_iff[symmetric])      
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square.
    have "0 = (\<Sum>\<^sub>ai::'a. 0)" by auto
    also have "\<dots> \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)"
    proof (rule infsetsum_mono_complex)
      show "(\<lambda>i. 0::complex) abs_summable_on (UNIV::'a set)"
        by simp        
      show "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
        by (simp add: sum)        
      show "0 \<le> cnj (f x) * f x"
        if "x \<in> UNIV"
        for x :: 'a and f :: "'a \<Rightarrow>_"
        using that
        by simp 
    qed
    finally show "0 \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)" by assumption
  qed

  show "(cinner x x = 0) = (x = 0)"
  proof (transfer, auto)
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence "(\<lambda>i::'a. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square
      by (metis (no_types, lifting) abs_summable_on_cong complex_mod_cnj norm_mult) 
    hence cmod_x2: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square
      by simp
    assume eq0: "(\<Sum>\<^sub>ai. cnj (x i) * x i) = 0"
    show "x = (\<lambda>_. 0)"
    proof (rule ccontr)
      assume "x \<noteq> (\<lambda>_. 0)"
      then obtain i where "x i \<noteq> 0" by auto
      hence "0 < cnj (x i) * x i"
        by (metis le_less cnj_x_x_geq0 complex_cnj_zero_iff vector_space_over_itself.scale_eq_0_iff)
      also have "\<dots> = (\<Sum>\<^sub>ai\<in>{i}. cnj (x i) * x i)" by auto
      also have "\<dots> \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)"
      proof (rule infsetsum_subset_complex)
        show "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
          by (simp add: cmod_x2)          
        show "{i} \<subseteq> UNIV"
          by simp          
        show "0 \<le> cnj (f x) * f x"
          if "x \<notin> {i}"
          for x :: 'a and f::"'a \<Rightarrow> _"
          using that
          by simp 
      qed
      also from eq0 have "\<dots> = 0" by assumption
      finally show False by simp
    qed
  qed

  show "norm x = sqrt (cmod (cinner x x))"
  proof transfer 
    fix x :: "'a \<Rightarrow> complex" 
    assume x: "has_ell2_norm x"
    have "(\<lambda>i::'a. cmod (x i) * cmod (x i)) abs_summable_on UNIV \<Longrightarrow>
    (\<lambda>i::'a. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      by (simp del: abs_summable_on_norm_iff add: norm_mult has_ell2_norm_infsetsum power2_eq_square)
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      using x
      unfolding has_ell2_norm_infsetsum power2_eq_square
      by auto
    from x have "ell2_norm x = sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2)"
    proof (subst ell2_norm_infsetsum)
      show "has_ell2_norm x"
        if "has_ell2_norm x"
        using that.
      show "sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2) = sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2)"
        if "has_ell2_norm x"
        using that
        by simp 
    qed
    also have "\<dots> = sqrt (\<Sum>\<^sub>ai. cmod (cnj (x i) * x i))"
      unfolding norm_complex_def power2_eq_square by auto
    also have "\<dots> = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))"
    proof (subst infsetsum_cmod)
      show "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
        by (simp add: sum)        
      show "0 \<le> cnj (f x) * f x"
        if "(x::'a) \<in> UNIV"
        for x :: 'a and f::"'a \<Rightarrow> _"
        using that
        by simp 
      show "sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i)) = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))"
        by simp        
    qed
    finally show "ell2_norm x = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))" by assumption
  qed
qed
end

instance ell2 :: (type) chilbert_space
proof
  fix X :: \<open>nat \<Rightarrow> 'a ell2\<close>
  define x where \<open>x n a = Rep_ell2 (X n) a\<close> for n a
  have [simp]: \<open>has_ell2_norm (x n)\<close> for n
    using Rep_ell2 x_def[abs_def] by simp

  assume \<open>Cauchy X\<close>
  moreover have "dist (x n a) (x m a) \<le> dist (X n) (X m)" for n m a
    by (metis Rep_ell2 x_def dist_norm ell2_norm_point_bound mem_Collect_eq minus_ell2.rep_eq norm_ell2.rep_eq)
  ultimately have \<open>Cauchy (\<lambda>n. x n a)\<close> for a
    by (meson Cauchy_def le_less_trans)
  then obtain l where x_lim: \<open>(\<lambda>n. x n a) \<longlonglongrightarrow> l a\<close> for a
    apply atomize_elim apply (rule choice)
    by (simp add: convergent_eq_Cauchy)
  define L where \<open>L = Abs_ell2 l\<close>
  define normF where \<open>normF F x = L2_set (cmod \<circ> x) F\<close> for F :: \<open>'a set\<close> and x
  have normF_triangle: \<open>normF F (\<lambda>a. x a + y a) \<le> normF F x + normF F y\<close> if \<open>finite F\<close> for F x y
  proof -
    have \<open>normF F (\<lambda>a. x a + y a) = L2_set (\<lambda>a. cmod (x a + y a)) F\<close>
      by (metis (mono_tags, lifting) L2_set_cong comp_apply normF_def)
    also have \<open>\<dots> \<le> L2_set (\<lambda>a. cmod (x a) + cmod (y a)) F\<close>
      by (meson L2_set_mono norm_ge_zero norm_triangle_ineq)
    also have \<open>\<dots> \<le> L2_set (\<lambda>a. cmod (x a)) F + L2_set (\<lambda>a. cmod (y a)) F\<close>
      by (simp add: L2_set_triangle_ineq)
    also have \<open>\<dots> \<le> normF F x + normF F y\<close>
      by (smt (verit, best) L2_set_cong normF_def comp_apply)
    finally show ?thesis
      by -
  qed
  have normF_negate: \<open>normF F (\<lambda>a. - x a) = normF F x\<close> if \<open>finite F\<close> for F x
    unfolding normF_def o_def by simp
  have normF_ell2norm: \<open>normF F x \<le> ell2_norm x\<close> if \<open>finite F\<close> and \<open>has_ell2_norm x\<close> for F x
    apply (auto intro!: cSUP_upper2[where x=F] simp: that normF_def ell2_norm_L2_set)
    by (meson has_ell2_norm_L2_set that(2))

  note Lim_bounded2[rotated, rule_format, trans]

  from \<open>Cauchy X\<close>
  obtain I where cauchyX: \<open>norm (X n - X m) \<le> \<epsilon>\<close> if \<open>\<epsilon>>0\<close> \<open>n\<ge>I \<epsilon>\<close> \<open>m\<ge>I \<epsilon>\<close> for \<epsilon> n m
    by (metis Cauchy_def dist_norm less_eq_real_def)
  have normF_xx: \<open>normF F (\<lambda>a. x n a - x m a) \<le> \<epsilon>\<close> if \<open>finite F\<close> \<open>\<epsilon>>0\<close> \<open>n\<ge>I \<epsilon>\<close> \<open>m\<ge>I \<epsilon>\<close> for \<epsilon> n m F
    apply (subst asm_rl[of \<open>(\<lambda>a. x n a - x m a) = Rep_ell2 (X n - X m)\<close>])
     apply (simp add: x_def minus_ell2.rep_eq)
    using that cauchyX by (metis Rep_ell2 mem_Collect_eq normF_ell2norm norm_ell2.rep_eq order_trans)
  have normF_xl_lim: \<open>(\<lambda>m. normF F (\<lambda>a. x m a - l a)) \<longlonglongrightarrow> 0\<close> if \<open>finite F\<close> for F
  proof -
    have \<open>(\<lambda>xa. cmod (x xa m - l m)) \<longlonglongrightarrow> 0\<close> for m
      using x_lim by (simp add: LIM_zero_iff tendsto_norm_zero)
    then have \<open>(\<lambda>m. \<Sum>i\<in>F. ((cmod \<circ> (\<lambda>a. x m a - l a)) i)\<^sup>2) \<longlonglongrightarrow> 0\<close>
      by (auto intro: tendsto_null_sum)
    then show ?thesis
      unfolding normF_def L2_set_def
      using tendsto_real_sqrt by force
  qed
  have normF_xl: \<open>normF F (\<lambda>a. x n a - l a) \<le> \<epsilon>\<close>
    if \<open>n \<ge> I \<epsilon>\<close> and \<open>\<epsilon> > 0\<close> and \<open>finite F\<close> for n \<epsilon> F
  proof -
    have \<open>normF F (\<lambda>a. x n a - l a) - \<epsilon> \<le> normF F (\<lambda>a. x n a - x m a) + normF F (\<lambda>a. x m a - l a) - \<epsilon>\<close> for m
      using normF_triangle[OF \<open>finite F\<close>, where x=\<open>(\<lambda>a. x n a - x m a)\<close> and y=\<open>(\<lambda>a. x m a - l a)\<close>]
      by auto
    also have \<open>\<dots> m \<le> normF F (\<lambda>a. x m a - l a)\<close> if \<open>m \<ge> I \<epsilon>\<close> for m
      using normF_xx[OF \<open>finite F\<close> \<open>\<epsilon>>0\<close> \<open>n \<ge> I \<epsilon>\<close> \<open>m \<ge> I \<epsilon>\<close>]
      by auto
    also have \<open>(\<lambda>m. \<dots> m) \<longlonglongrightarrow> 0\<close>
      using \<open>finite F\<close> by (rule normF_xl_lim)
    finally show ?thesis
      by auto
  qed
  have \<open>normF F l \<le> 1 + normF F (x (I 1))\<close> if [simp]: \<open>finite F\<close> for F
    using normF_xl[where F=F and \<epsilon>=1 and n=\<open>I 1\<close>]
    using normF_triangle[where F=F and x=\<open>x (I 1)\<close> and y=\<open>\<lambda>a. l a - x (I 1) a\<close>]
    using normF_negate[where F=F and x=\<open>(\<lambda>a. x (I 1) a - l a)\<close>]
    by auto
  also have \<open>\<dots> F \<le> 1 + ell2_norm (x (I 1))\<close> if \<open>finite F\<close> for F
    using normF_ell2norm that by simp
  finally have [simp]: \<open>has_ell2_norm l\<close>
    unfolding has_ell2_norm_L2_set
    by (auto intro!: bdd_aboveI simp flip: normF_def)
  then have \<open>l = Rep_ell2 L\<close>
    by (simp add: Abs_ell2_inverse L_def)
  have [simp]: \<open>has_ell2_norm (\<lambda>a. x n a - l a)\<close> for n
    apply (subst diff_conv_add_uminus)
    apply (rule ell2_norm_triangle)
    by (auto intro!: ell2_norm_uminus)
  from normF_xl have ell2norm_xl: \<open>ell2_norm (\<lambda>a. x n a - l a) \<le> \<epsilon>\<close>
    if \<open>n \<ge> I \<epsilon>\<close> and \<open>\<epsilon> > 0\<close> for n \<epsilon>
    apply (subst ell2_norm_L2_set)
    using that by (auto intro!: cSUP_least simp: normF_def)
  have \<open>norm (X n - L) \<le> \<epsilon>\<close> if \<open>n \<ge> I \<epsilon>\<close> and \<open>\<epsilon> > 0\<close> for n \<epsilon>
    using ell2norm_xl[OF that]
    apply (simp add: x_def norm_ell2.rep_eq \<open>l = Rep_ell2 L\<close>)
    by (smt (verit, best) SUP_cong ell2_norm_def minus_ell2.rep_eq sum.cong)
  then have \<open>X \<longlonglongrightarrow> L\<close>
    unfolding tendsto_iff
    apply (auto simp: dist_norm eventually_sequentially)
    by (meson field_lbound_gt_zero le_less_trans)
  then show \<open>convergent X\<close>
    by (rule convergentI)
qed

instantiation ell2 :: (CARD_1) complex_algebra_1 
begin
lift_definition one_ell2 :: "'a ell2" is "\<lambda>_. 1" by simp
lift_definition times_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b x. a x * b x"
  by simp   
instance 
proof
  fix a b c :: "'a ell2" and r :: complex
  show "a * b * c = a * (b * c)"
    by (transfer, auto)
  show "(a + b) * c = a * c + b * c"
    apply (transfer, rule ext)
    by (simp add: distrib_left mult.commute)
  show "a * (b + c) = a * b + a * c"
    apply transfer
    by (simp add: ring_class.ring_distribs(1))
  show "r *\<^sub>C a * b = r *\<^sub>C (a * b)"
    by (transfer, auto)
  show "(a::'a ell2) * r *\<^sub>C b = r *\<^sub>C (a * b)"
    by (transfer, auto)
  show "1 * a = a"
    by (transfer, rule ext, auto)
  show "a * 1 = a"
    by (transfer, rule ext, auto)
  show "(0::'a ell2) \<noteq> 1"
    apply transfer
    by (meson zero_neq_one)
qed
end

instantiation ell2 :: (CARD_1) field begin
lift_definition divide_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b x. a x / b x"
  by simp   
lift_definition inverse_ell2 :: "'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a x. inverse (a x)"
  by simp
instance
proof (intro_classes; transfer)
  fix a :: "'a \<Rightarrow> complex"
  assume "a \<noteq> (\<lambda>_. 0)"
  then obtain y where ay: "a y \<noteq> 0"
    by auto
  show "(\<lambda>x. inverse (a x) * a x) = (\<lambda>_. 1)"
  proof (rule ext)
    fix x
    have "x = y"
      by auto
    with ay have "a x \<noteq> 0"
      by metis
    then show "inverse (a x) * a x = 1"
      by auto
  qed
qed (auto simp add: divide_complex_def mult.commute ring_class.ring_distribs)
end


subsection \<open>Orthogonality\<close>

lemma ell2_pointwise_ortho:
  assumes \<open>\<And> i. Rep_ell2 x i = 0 \<or> Rep_ell2 y i = 0\<close>
  shows \<open>is_orthogonal x y\<close>
  using assms apply transfer
  by (simp add: infsetsum_all_0)


subsection \<open>Truncated vectors\<close>

lift_definition trunc_ell2:: \<open>'a set \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2\<close>
  is \<open>\<lambda> S x. (\<lambda> i. (if i \<in> S then x i else 0))\<close>
  unfolding has_ell2_norm_def
  apply (rule bdd_above_image_mono)
  by (auto intro!: sum_mono)

lemma trunc_ell2_empty[simp]: \<open>trunc_ell2 {} x = 0\<close>
  apply transfer by simp

lemma norm_id_minus_trunc_ell2:
  \<open>(norm (x - trunc_ell2 S x))^2 = (norm x)^2 - (norm (trunc_ell2 S x))^2\<close>
proof-
  have \<open>Rep_ell2 (trunc_ell2 S x) i = 0 \<or> Rep_ell2 (x - trunc_ell2 S x) i = 0\<close> for i
    apply transfer
    by auto
  hence \<open>\<langle> (trunc_ell2 S x), (x - trunc_ell2 S x) \<rangle> = 0\<close>
    using ell2_pointwise_ortho by blast
  hence \<open>(norm x)^2 = (norm (trunc_ell2 S x))^2 + (norm (x - trunc_ell2 S x))^2\<close>
    using pythagorean_theorem by fastforce    
  thus ?thesis by simp
qed

lemma norm_trunc_ell2_finite:
  \<open>finite S \<Longrightarrow> (norm (trunc_ell2 S x)) = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S)\<close>
proof-
  assume \<open>finite S\<close>
  moreover have \<open>\<And> i. i \<notin> S \<Longrightarrow> Rep_ell2 ((trunc_ell2 S x)) i = 0\<close>
    by (simp add: trunc_ell2.rep_eq)    
  ultimately have \<open>(norm (trunc_ell2 S x)) = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 ((trunc_ell2 S x)) i))\<^sup>2)) S)\<close>
    using ell2_norm_finite_support
    by blast 
  moreover have \<open>\<And> i. i \<in> S \<Longrightarrow> Rep_ell2 ((trunc_ell2 S x)) i = Rep_ell2 x i\<close>
    by (simp add: trunc_ell2.rep_eq)
  ultimately show ?thesis by simp
qed

lemma trunc_ell2_lim_at_UNIV:
  \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
proof -
  define f where \<open>f i = (cmod (Rep_ell2 \<psi> i))\<^sup>2\<close> for i

  have has: \<open>has_ell2_norm (Rep_ell2 \<psi>)\<close>
    using Rep_ell2 by blast
  then have summable: "f abs_summable_on UNIV"
    using f_def has_ell2_norm_infsetsum by fastforce

  have \<open>norm \<psi> = (ell2_norm (Rep_ell2 \<psi>))\<close>
    apply transfer by simp
  also have \<open>\<dots> = sqrt (infsetsum' f UNIV)\<close>
    unfolding ell2_norm_infsetsum[OF has] f_def[symmetric]
    using summable by (simp add: infsetsum_infsetsum')
  finally have norm\<psi>: \<open>norm \<psi> = sqrt (infsetsum' f UNIV)\<close>
    by -

  have norm_trunc: \<open>norm (trunc_ell2 S \<psi>) = sqrt (sum f S)\<close> if \<open>finite S\<close> for S
    using f_def that norm_trunc_ell2_finite by fastforce

  have \<open>(sum f \<longlongrightarrow> infsetsum' f UNIV) (finite_subsets_at_top UNIV)\<close>
    by (simp add: abs_summable_infsetsum'_converges infsetsum'_tendsto summable)
  then have \<open>((\<lambda>S. sqrt (sum f S)) \<longlongrightarrow> sqrt (infsetsum' f UNIV)) (finite_subsets_at_top UNIV)\<close>
    using tendsto_real_sqrt by blast
  then have \<open>((\<lambda>S. norm (trunc_ell2 S \<psi>)) \<longlongrightarrow> norm \<psi>) (finite_subsets_at_top UNIV)\<close>
    apply (subst tendsto_cong[where g=\<open>\<lambda>S. sqrt (sum f S)\<close>])
    by (auto simp add: eventually_finite_subsets_at_top_weakI norm_trunc norm\<psi>)
  then have \<open>((\<lambda>S. (norm (trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top UNIV)\<close>
    by (simp add: tendsto_power)
  then have \<open>((\<lambda>S. (norm \<psi>)\<^sup>2 - (norm (trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    apply (rule tendsto_diff[where a=\<open>(norm \<psi>)^2\<close> and b=\<open>(norm \<psi>)^2\<close>, simplified, rotated])
    by auto
  then have \<open>((\<lambda>S. (norm (\<psi> - trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    unfolding norm_id_minus_trunc_ell2 by simp
  then have \<open>((\<lambda>S. norm (\<psi> - trunc_ell2 S \<psi>)) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    by auto
  then have \<open>((\<lambda>S. \<psi> - trunc_ell2 S \<psi>) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    by (rule tendsto_norm_zero_cancel)
  then show ?thesis
    apply (rule Lim_transform2[where f=\<open>\<lambda>_. \<psi>\<close>, rotated])
    by simp
qed

subsection \<open>Kets and bras\<close>

lift_definition ket :: "'a \<Rightarrow> 'a ell2" is "\<lambda>x y. if x=y then 1 else 0"
  by (rule has_ell2_norm_ket)

abbreviation bra :: "'a \<Rightarrow> (_,complex) cblinfun" where "bra i \<equiv> vector_to_cblinfun (ket i)*" for i

instance ell2 :: (type) not_singleton
proof standard
  have "ket undefined \<noteq> (0::'a ell2)"
  proof transfer
    show "(\<lambda>y. if (undefined::'a) = y then 1::complex else 0) \<noteq> (\<lambda>_. 0)"
      by (meson one_neq_zero)
  qed   
  thus \<open>\<exists>x y::'a ell2. x \<noteq> y\<close>
    by blast    
qed

lemma cinner_ket_left: \<open>\<langle>ket i, \<psi>\<rangle> = Rep_ell2 \<psi> i\<close>
  apply (transfer fixing: i)
  apply (subst infsetsum_cong_neutral[where B=\<open>{i}\<close>])
  by auto

lemma cinner_ket_right: \<open>\<langle>\<psi>, ket i\<rangle> = cnj (Rep_ell2 \<psi> i)\<close>
  apply (transfer fixing: i)
  apply (subst infsetsum_cong_neutral[where B=\<open>{i}\<close>])
  by auto

lemma cinner_ket_eqI:
  assumes \<open>\<And>i. cinner (ket i) \<psi> = cinner (ket i) \<phi>\<close>
  shows \<open>\<psi> = \<phi>\<close>
  by (metis Rep_ell2_inject assms cinner_ket_left ext)

lemma norm_ket[simp]: "norm (ket i) = 1"
  apply transfer by (rule ell2_norm_ket)

lemma cinner_ket_same[simp]:
  \<open>\<langle>ket i, ket i\<rangle> = 1\<close>
proof-
  have \<open>norm (ket i) = 1\<close>
    by simp
  hence \<open>sqrt (cmod \<langle>ket i, ket i\<rangle>) = 1\<close>
    by (metis norm_eq_sqrt_cinner)
  hence \<open>cmod \<langle>ket i, ket i\<rangle> = 1\<close>
    using real_sqrt_eq_1_iff by blast
  moreover have \<open>\<langle>ket i, ket i\<rangle> = cmod \<langle>ket i, ket i\<rangle>\<close>
  proof-
    have \<open>\<langle>ket i, ket i\<rangle> \<in> \<real>\<close>
      by (simp add: cinner_real)      
    thus ?thesis 
      by (metis cinner_ge_zero complex_of_real_cmod) 
  qed
  ultimately show ?thesis by simp
qed

lemma orthogonal_ket[simp]:
  \<open>is_orthogonal (ket i) (ket j) \<longleftrightarrow> i \<noteq> j\<close>
  by (simp add: cinner_ket_left ket.rep_eq)

lemma cinner_ket: \<open>\<langle>ket i, ket j\<rangle> = (if i=j then 1 else 0)\<close>
  by (simp add: cinner_ket_left ket.rep_eq)

lemma ket_injective[simp]: \<open>ket i = ket j \<longleftrightarrow> i = j\<close>
  by (metis cinner_ket one_neq_zero)

lemma inj_ket[simp]: \<open>inj ket\<close>
  by (simp add: inj_on_def)


lemma trunc_ell2_ket_cspan:
  \<open>trunc_ell2 S x \<in> (cspan (range ket))\<close> if \<open>finite S\<close>
proof (use that in induction)
  case empty
  then show ?case 
    by (auto intro: complex_vector.span_zero)
next
  case (insert a F)
  from insert.hyps have \<open>trunc_ell2 (insert a F) x = trunc_ell2 F x + Rep_ell2 x a *\<^sub>C ket a\<close>
    apply (transfer fixing: F a)
    by auto
  with insert.IH
  show ?case
    by (simp add: complex_vector.span_add_eq complex_vector.span_base complex_vector.span_scale)
qed

lemma closed_cspan_range_ket[simp]:
  \<open>closure (cspan (range ket)) = UNIV\<close>
proof (intro set_eqI iffI UNIV_I closure_approachable[THEN iffD2] allI impI)
  fix \<psi> :: \<open>'a ell2\<close>
  fix e :: real assume \<open>e > 0\<close>
  have \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
    by (rule trunc_ell2_lim_at_UNIV)
  then obtain F where \<open>finite F\<close> and \<open>dist (trunc_ell2 F \<psi>) \<psi> < e\<close>
    apply (drule_tac tendstoD[OF _ \<open>e > 0\<close>])
    by (auto dest: simp: eventually_finite_subsets_at_top)
  moreover have \<open>trunc_ell2 F \<psi> \<in> cspan (range ket)\<close>
    using \<open>finite F\<close> trunc_ell2_ket_cspan by blast
  ultimately show \<open>\<exists>\<phi>\<in>cspan (range ket). dist \<phi> \<psi> < e\<close>
    by auto
qed

lemma ccspan_range_ket[simp]: "ccspan (range ket) = (top::('a ell2 ccsubspace))"
proof-
  have \<open>closure (complex_vector.span (range ket)) = (UNIV::'a ell2 set)\<close>
    using Complex_L2.closed_cspan_range_ket by blast
  thus ?thesis
    by (simp add: ccspan.abs_eq top_ccsubspace.abs_eq)
qed

lemma cspan_range_ket_finite[simp]: "cspan (range ket :: 'a::finite ell2 set) = UNIV"
  by (metis closed_cspan_range_ket closure_finite_cspan finite_class.finite_UNIV finite_imageI)

instance ell2 :: (finite) cfinite_dim
proof
  define basis :: \<open>'a ell2 set\<close> where \<open>basis = range ket\<close>
  have \<open>finite basis\<close>
    unfolding basis_def by simp
  moreover have \<open>cspan basis = UNIV\<close>
    by (simp add: basis_def)
  ultimately show \<open>\<exists>basis::'a ell2 set. finite basis \<and> cspan basis = UNIV\<close>
    by auto
qed

instantiation ell2 :: (enum) onb_enum begin
definition "canonical_basis_ell2 = map ket Enum.enum"
instance
proof
  show "distinct (canonical_basis::'a ell2 list)"
  proof-
    have \<open>finite (UNIV::'a set)\<close>
      by simp
    have \<open>distinct (enum_class.enum::'a list)\<close>
      using enum_distinct by blast
    moreover have \<open>inj_on ket (set enum_class.enum)\<close>
      by (meson inj_onI ket_injective)         
    ultimately show ?thesis
      unfolding canonical_basis_ell2_def
      using distinct_map
      by blast
  qed    

  show "is_ortho_set (set (canonical_basis::'a ell2 list))"
    apply (auto simp: canonical_basis_ell2_def enum_UNIV)
    by (smt (z3) norm_ket f_inv_into_f is_ortho_set_def orthogonal_ket norm_zero)

  show "cindependent (set (canonical_basis::'a ell2 list))"
    apply (auto simp: canonical_basis_ell2_def enum_UNIV)
    by (smt (verit, best) norm_ket f_inv_into_f is_ortho_set_def is_ortho_set_cindependent orthogonal_ket norm_zero)

  show "cspan (set (canonical_basis::'a ell2 list)) = UNIV"
    by (auto simp: canonical_basis_ell2_def enum_UNIV)

  show "norm (x::'a ell2) = 1"
    if "(x::'a ell2) \<in> set canonical_basis"
    for x :: "'a ell2"
    using that unfolding canonical_basis_ell2_def 
    by auto
qed

end

lemma canonical_basis_length_ell2[code_unfold, simp]:
  "length (canonical_basis ::'a::enum ell2 list) = CARD('a)"
  unfolding canonical_basis_ell2_def apply simp
  using card_UNIV_length_enum by metis

lemma ket_canonical_basis: "ket x = canonical_basis ! enum_idx x"
proof-
  have "x = (enum_class.enum::'a list) ! enum_idx x"
    using enum_idx_correct[where i = x] by simp
  hence p1: "ket x = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by simp
  have "enum_idx x < length (enum_class.enum::'a list)"
    using enum_idx_bound[where x = x].
  hence "(map ket (enum_class.enum::'a list)) ! enum_idx x 
        = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by auto      
  thus ?thesis
    unfolding canonical_basis_ell2_def using p1 by auto    
qed

lemma clinear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>clinear f\<close>
  assumes \<open>clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule complex_vector.linear_eq_on_span[where f=f and g=g and B=\<open>range ket\<close>])
  using assms by auto

lemma equal_ket:
  fixes A B :: \<open>('a ell2, 'b::complex_normed_vector) cblinfun\<close>
  assumes \<open>\<And> x. cblinfun_apply A (ket x) = cblinfun_apply B (ket x)\<close>
  shows \<open>A = B\<close>
  apply (rule cblinfun_eq_gen_eqI[where G=\<open>range ket\<close>])
  using assms by auto

lemma antilinear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>antilinear f\<close>
  assumes \<open>antilinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
proof -
  have [simp]: \<open>clinear (f \<circ> from_conjugate_space)\<close>
    apply (rule antilinear_o_antilinear)
    using assms by (simp_all add: antilinear_from_conjugate_space)
  have [simp]: \<open>clinear (g \<circ> from_conjugate_space)\<close>
    apply (rule antilinear_o_antilinear)
    using assms by (simp_all add: antilinear_from_conjugate_space)
  have [simp]: \<open>cspan (to_conjugate_space ` (range ket :: 'a ell2 set)) = UNIV\<close>
    by simp
  have "f o from_conjugate_space = g o from_conjugate_space"
    apply (rule ext)
    apply (rule complex_vector.linear_eq_on_span[where f="f o from_conjugate_space" and g="g o from_conjugate_space" and B=\<open>to_conjugate_space ` range ket\<close>])
       apply (simp, simp)
    using assms(3) by (auto simp: to_conjugate_space_inverse)
  then show "f = g"
    by (smt (verit) UNIV_I from_conjugate_space_inverse surj_def surj_fun_eq to_conjugate_space_inject) 
qed

lemma cinner_ket_adjointI:
  fixes F::"'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _" and G::"'b ell2 \<Rightarrow>\<^sub>C\<^sub>L_"
  assumes "\<And> i j. \<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>"
  shows "F = G*"
proof -
  from assms
  have \<open>(F *\<^sub>V x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (G *\<^sub>V y)\<close> if \<open>x \<in> range ket\<close> and \<open>y \<in> range ket\<close> for x y
    using that by auto
  then have \<open>(F *\<^sub>V x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (G *\<^sub>V y)\<close> if \<open>x \<in> range ket\<close> for x y
    apply (rule bounded_clinear_eq_on[where G=\<open>range ket\<close> and t=y, rotated 2])
    using that by (auto intro!: bounded_linear_intros)
  then have \<open>(F *\<^sub>V x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (G *\<^sub>V y)\<close> for x y
    apply (rule bounded_antilinear_eq_on[where G=\<open>range ket\<close> and t=x, rotated 2])
    by (auto intro!: bounded_linear_intros)
  then show ?thesis
    by (rule adjoint_eqI)
qed

lemma ket_nonzero[simp]: "ket i \<noteq> 0"
  using norm_ket[of i] by force


lemma cindependent_ket:
  "cindependent (range (ket::'a\<Rightarrow>_))"
proof-
  define S where "S = range (ket::'a\<Rightarrow>_)"
  have "is_ortho_set S"
    unfolding S_def is_ortho_set_def by auto
  moreover have "0 \<notin> S"
    unfolding S_def
    using ket_nonzero
    by (simp add: image_iff)
  ultimately show ?thesis
    using is_ortho_set_cindependent[where A = S] unfolding S_def 
    by blast
qed

lemma cdim_UNIV_ell2[simp]: \<open>cdim (UNIV::'a::finite ell2 set) = CARD('a)\<close>
  apply (subst cspan_range_ket_finite[symmetric])
  by (metis card_image cindependent_ket complex_vector.dim_span_eq_card_independent inj_ket)

lemma is_ortho_set_ket[simp]: \<open>is_ortho_set (range ket)\<close>
  using is_ortho_set_def by fastforce

subsection \<open>Butterflies\<close>

lemma cspan_butterfly_ket: \<open>cspan {butterfly (ket i) (ket j)| (i::'b::finite) (j::'a::finite). True} = UNIV\<close>
proof -
  have *: \<open>{butterfly (ket i) (ket j)| (i::'b::finite) (j::'a::finite). True} = {butterfly a b |a b. a \<in> range ket \<and> b \<in> range ket}\<close>
    by auto
  show ?thesis
    apply (subst *)
    apply (rule cspan_butterfly_UNIV)
    by auto
qed

lemma cindependent_butterfly_ket: \<open>cindependent {butterfly (ket i) (ket j)| (i::'b) (j::'a). True}\<close>
proof -
  have *: \<open>{butterfly (ket i) (ket j)| (i::'b) (j::'a). True} = {butterfly a b |a b. a \<in> range ket \<and> b \<in> range ket}\<close>
    by auto
  show ?thesis
    apply (subst *)
    apply (rule cindependent_butterfly)
    by auto
qed

lemma clinear_eq_butterfly_ketI:
  fixes F G :: \<open>('a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2) \<Rightarrow> 'c::complex_vector\<close>
  assumes "clinear F" and "clinear G"
  assumes "\<And>i j. F (butterfly (ket i) (ket j)) = G (butterfly (ket i) (ket j))"
  shows "F = G"
  apply (rule complex_vector.linear_eq_on_span[where f=F, THEN ext, rotated 3])
     apply (subst cspan_butterfly_ket)
  using assms by auto

lemma sum_butterfly_ket[simp]: \<open>(\<Sum>(i::'a::finite)\<in>UNIV. butterfly (ket i) (ket i)) = id_cblinfun\<close>
  apply (rule equal_ket)
  apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>y. y *\<^sub>V ket _\<close>])
   apply (auto simp add: scaleC_cblinfun.rep_eq cblinfun.add_left clinearI butterfly_def cblinfun_compose_image cinner_ket)
  apply (subst sum.mono_neutral_cong_right[where S=\<open>{_}\<close>])
  by auto

subsection \<open>One-dimensional spaces\<close>

instantiation ell2 :: ("{enum,CARD_1}") one_dim begin
text \<open>Note: enum is not needed logically, but without it this instantiation
            clashes with \<open>instantiation ell2 :: (enum) onb_enum\<close>\<close>
instance
proof
  show "canonical_basis = [1::'a ell2]"
    unfolding canonical_basis_ell2_def
    apply transfer
    by (simp add: enum_CARD_1[of undefined])
  show "a *\<^sub>C 1 * b *\<^sub>C 1 = (a * b) *\<^sub>C (1::'a ell2)" for a b
    apply (transfer fixing: a b) by simp
  show "x / y = x * inverse y" for x y :: "'a ell2"
    by (simp add: divide_inverse)
  show "inverse (c *\<^sub>C 1) = inverse c *\<^sub>C (1::'a ell2)" for c :: complex
    apply transfer by auto
qed
end


subsection \<open>Classical operators\<close>

text \<open>We call an operator mapping \<^term>\<open>ket x\<close> to \<^term>\<open>ket (\<pi> x)\<close> or \<^term>\<open>0\<close> "classical".
(The meaning is inspired by the fact that in quantum mechanics, such operators usually correspond
to operations with classical interpretation (such as Pauli-X, CNOT, measurement in the computational
basis, etc.))\<close>

definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L'b ell2" where
  "classical_operator \<pi> = 
    (let f = (\<lambda>t. (case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i))
     in
      cblinfun_extension (range (ket::'a\<Rightarrow>_)) f)"


definition "classical_operator_exists \<pi> \<longleftrightarrow>
  cblinfun_extension_exists (range ket)
    (\<lambda>t. case \<pi> (inv ket t) of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)"

lemma classical_operator_existsI:
  assumes "\<And>x. B *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  shows "classical_operator_exists \<pi>"
  unfolding classical_operator_exists_def
  apply (rule cblinfun_extension_existsI[of _ B])
  using assms 
  by (auto simp: inv_f_f[OF inj_ket])

lemma classical_operator_exists_inj:
  assumes "inj_map \<pi>"
  shows "classical_operator_exists \<pi>"
    (* Probably a shorter proof is possible using cblinfun_extension_exists_bounded_dense *)
proof -
  define C0 where "C0 \<psi> = (\<lambda>b. case inv_map \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)" for \<psi> :: "'a\<Rightarrow>complex"

  have has_ell2_norm_C0: \<open>has_ell2_norm \<psi> \<Longrightarrow> has_ell2_norm (C0 \<psi>)\<close> for \<psi>
  proof -
    assume \<open>has_ell2_norm \<psi>\<close>
    hence \<open>bdd_above (sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) ` Collect finite)\<close>
      unfolding has_ell2_norm_def
      by blast
    hence \<open>\<exists> M. \<forall> S. finite S \<longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> M\<close>
      by (simp add: bdd_above_def)
    then obtain M::real where \<open>\<And> S::'a set. finite S \<Longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> M\<close>
      by blast
    define \<phi>::\<open>'b \<Rightarrow> complex\<close> where
      \<open>\<phi> b = (case inv_map \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)\<close> for b
    have \<open>\<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> M\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close> and \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      from  \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      have  \<open>\<forall>i\<in>R. \<exists> x. Some x = inv_map \<pi> i\<close>
        unfolding \<phi>_def
        by (metis option.case_eq_if option.collapse)
      hence  \<open>\<exists> f. \<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close>
        by metis
      then obtain f::\<open>'b\<Rightarrow>'a\<close> where \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
        by blast
      define S::\<open>'a set\<close> where \<open>S = f ` R\<close>
      have \<open>finite S\<close>
        using \<open>finite R\<close>
        by (simp add: S_def)
      moreover have \<open>(\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) =  (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2)\<close>
      proof-
        have \<open>inj_on f R\<close>
        proof(rule inj_onI)
          fix x y :: 'b
          assume \<open>x \<in> R\<close> and \<open>y \<in> R\<close> and \<open>f x = f y\<close>
          from \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
          have \<open>\<forall>i\<in>R. Some (f i) = Some (inv \<pi> (Some i))\<close>
            by (metis inv_map_def option.distinct(1))
          hence \<open>\<forall>i\<in>R. f i = inv \<pi> (Some i)\<close>
            by blast
          hence \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close>
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> f_inv_into_f inv_map_def option.distinct(1)) 
          have \<open>\<pi> (f x) = Some x\<close>
            using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>x\<in>R\<close> by blast
          moreover have \<open>\<pi> (f y) = Some y\<close>
            using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>y\<in>R\<close> by blast
          ultimately have \<open>Some x = Some y\<close>
            using \<open>f x = f y\<close> by metis
          thus \<open>x = y\<close> by simp
        qed
        moreover have \<open>i \<in> R \<Longrightarrow> (cmod (\<phi> i))\<^sup>2 = (cmod (\<psi> (f i)))\<^sup>2\<close>
          for i
        proof-
          assume \<open>i \<in> R\<close>
          hence \<open>\<phi> i = \<psi> (f i)\<close>
            unfolding \<phi>_def
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> option.simps(5))
          thus ?thesis
            by simp 
        qed
        ultimately show ?thesis unfolding S_def
          by (metis (mono_tags, lifting) sum.reindex_cong)
      qed
      ultimately show ?thesis
        by (simp add: \<open>\<And>S. finite S \<Longrightarrow> (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2) \<le> M\<close>) 
    qed     
    have \<open>finite R \<Longrightarrow> ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) \<le> M\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close>
      define U::\<open>'b set\<close> where \<open>U = {i | i::'b. i \<in> R \<and>  \<phi> i \<noteq> 0 }\<close>
      define V::\<open>'b set\<close> where \<open>V = {i | i::'b. i \<in> R \<and>  \<phi> i = 0 }\<close>
      have \<open>U \<inter> V = {}\<close>
        unfolding U_def V_def by blast
      moreover have \<open>U \<union> V = R\<close>
        unfolding U_def V_def by blast
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) + 
            ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V )\<close>
        using \<open>finite R\<close> sum.union_disjoint by auto
      moreover have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V ) = 0\<close>
        unfolding V_def by auto
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
        by simp
      moreover have \<open>\<forall> i \<in> U. \<phi> i \<noteq> 0\<close>
        by (simp add: U_def)
      moreover have \<open>finite U\<close>
        unfolding U_def using \<open>finite R\<close>
        by simp
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) \<le> M\<close>
        using \<open>\<And>R. \<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> M\<close> by blast        
      thus ?thesis using \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
        by simp
    qed
    hence  \<open>bdd_above (sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) ` Collect finite)\<close>
      unfolding bdd_above_def
      by blast
    thus ?thesis
      unfolding \<phi>_def C0_def using has_ell2_norm_def by blast
  qed

  define C1 :: "('a ell2 \<Rightarrow> 'b ell2)"
    where "C1 \<psi> = Abs_ell2 (C0 (Rep_ell2 \<psi>))" for \<psi>
  have [transfer_rule]: "rel_fun (pcr_ell2 (=)) (pcr_ell2 (=)) C0 C1" 
    apply (rule rel_funI)
    unfolding ell2.pcr_cr_eq cr_ell2_def C1_def 
    apply (subst Abs_ell2_inverse)
    using has_ell2_norm_C0 Rep_ell2 by blast+

  have add: "C1 (x + y) = C1 x + C1 y" for x y
    apply transfer unfolding C0_def 
    apply (rule ext, rename_tac b)
    apply (case_tac "inv_map \<pi> b")
    by auto

  have scaleC: "C1 (c *\<^sub>C x) = c *\<^sub>C C1 x" for c x
    apply transfer unfolding C0_def 
    apply (rule ext, rename_tac b)
    apply (case_tac "inv_map \<pi> b")
    by auto

  have "clinear C1"
    using add scaleC by (rule clinearI)

  have bounded_C0: \<open>ell2_norm (C0 \<psi>) \<le> ell2_norm \<psi>\<close> if \<open>has_ell2_norm \<psi>\<close> for \<psi>  
  proof-
    have \<open>\<forall> S. finite S \<longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> (ell2_norm \<psi>)^2\<close>
      using \<open>has_ell2_norm \<psi>\<close> ell2_norm_def
      by (smt cSUP_upper has_ell2_norm_def mem_Collect_eq sqrt_le_D sum.cong)
    define \<phi>::\<open>'b \<Rightarrow> complex\<close> where
      \<open>\<phi> b = (case inv_map \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)\<close> for b
    have \<open>\<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le>  (ell2_norm \<psi>)^2\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close> and \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      from  \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      have  \<open>\<forall>i\<in>R. \<exists> x. Some x = inv_map \<pi> i\<close>
        unfolding \<phi>_def
        by (metis option.case_eq_if option.collapse)
      hence  \<open>\<exists> f. \<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close>
        by metis
      then obtain f::\<open>'b\<Rightarrow>'a\<close> where \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
        by blast
      define S::\<open>'a set\<close> where \<open>S = f ` R\<close>
      have \<open>finite S\<close>
        using \<open>finite R\<close>
        by (simp add: S_def)
      moreover have \<open>(\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) =  (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2)\<close>
      proof-
        have \<open>inj_on f R\<close>
        proof(rule inj_onI)
          fix x y :: 'b
          assume \<open>x \<in> R\<close> and \<open>y \<in> R\<close> and \<open>f x = f y\<close>
          from \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
          have \<open>\<forall>i\<in>R. Some (f i) = Some (inv \<pi> (Some i))\<close>
            by (metis inv_map_def option.distinct(1))
          hence \<open>\<forall>i\<in>R. f i = inv \<pi> (Some i)\<close>
            by blast
          hence \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close>
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> f_inv_into_f inv_map_def option.distinct(1)) 
          have \<open>\<pi> (f x) = Some x\<close>
            using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>x\<in>R\<close> by blast
          moreover have \<open>\<pi> (f y) = Some y\<close>
            using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>y\<in>R\<close> by blast
          ultimately have \<open>Some x = Some y\<close>
            using \<open>f x = f y\<close> by metis
          thus \<open>x = y\<close> by simp
        qed
        moreover have \<open>i \<in> R \<Longrightarrow> (cmod (\<phi> i))\<^sup>2 = (cmod (\<psi> (f i)))\<^sup>2\<close>
          for i
        proof-
          assume \<open>i \<in> R\<close>
          hence \<open>\<phi> i = \<psi> (f i)\<close>
            unfolding \<phi>_def
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> option.simps(5))
          thus ?thesis
            by simp 
        qed
        ultimately show ?thesis unfolding S_def
          by (metis (mono_tags, lifting) sum.reindex_cong)
      qed
      ultimately show ?thesis
        by (simp add: \<open>\<forall>S. finite S \<longrightarrow> (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2) \<le> (ell2_norm \<psi>)\<^sup>2\<close>)
    qed     
    have \<open>finite R \<Longrightarrow> ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) \<le> (ell2_norm \<psi>)\<^sup>2\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close>
      define U::\<open>'b set\<close> where \<open>U = {i | i::'b. i \<in> R \<and>  \<phi> i \<noteq> 0 }\<close>
      define V::\<open>'b set\<close> where \<open>V = {i | i::'b. i \<in> R \<and>  \<phi> i = 0 }\<close>
      have \<open>U \<inter> V = {}\<close>
        unfolding U_def V_def by blast
      moreover have \<open>U \<union> V = R\<close>
        unfolding U_def V_def by blast
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) + 
            ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V )\<close>
        using \<open>finite R\<close> sum.union_disjoint by auto
      moreover have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V ) = 0\<close>
        unfolding V_def by auto
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
        by simp
      moreover have \<open>\<forall> i \<in> U. \<phi> i \<noteq> 0\<close>
        by (simp add: U_def)
      moreover have \<open>finite U\<close>
        unfolding U_def using \<open>finite R\<close>
        by simp
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) \<le>  (ell2_norm \<psi>)\<^sup>2\<close>
        using \<open>\<And>R. \<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le>  (ell2_norm \<psi>)\<^sup>2\<close> by blast        
      thus ?thesis using \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
        by simp
    qed
    hence \<open>finite R \<Longrightarrow> sqrt (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> ell2_norm \<psi>\<close>
      for R
    proof-
      assume \<open>finite R\<close>
      hence \<open>(\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> (ell2_norm \<psi>)^2\<close>
        by (simp add: \<open>\<And>R. finite R \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> (ell2_norm \<psi>)\<^sup>2\<close>)
      hence \<open>sqrt (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> sqrt ((ell2_norm \<psi>)^2)\<close>
        using real_sqrt_le_iff by blast
      moreover have \<open>sqrt ((ell2_norm \<psi>)^2) = ell2_norm \<psi>\<close>
      proof-
        have \<open>ell2_norm \<psi> \<ge> 0\<close>
        proof-
          obtain X where \<open>Rep_ell2 X = \<psi>\<close>
            using Rep_ell2_cases \<open>has_ell2_norm \<psi>\<close> by auto
          have \<open>norm X \<ge> 0\<close>
            by simp
          thus \<open>ell2_norm \<psi> \<ge> 0\<close> 
            using \<open>Rep_ell2 X = \<psi>\<close>
            by (simp add: norm_ell2.rep_eq) 
        qed
        thus ?thesis
          by simp 
      qed
      ultimately show ?thesis
        by linarith 
    qed
    hence \<open>\<forall> L \<in> { sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F} }. L \<le> ell2_norm \<psi>\<close>
      by blast
    moreover have \<open>{ sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F} } \<noteq> {}\<close>
      by force
    ultimately have \<open>Sup { sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F} } \<le> ell2_norm \<psi>\<close>
      by (meson cSup_least)
    moreover have \<open>sqrt ( Sup { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} } )
          = Sup { sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F}  }\<close>
    proof-
      define T where \<open>T = { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} }\<close>
      have \<open>mono sqrt\<close>
        by (simp add: monoI)
      moreover have \<open>continuous (at_left (Sup T)) sqrt\<close>
        by (simp add: continuous_at_imp_continuous_at_within isCont_real_sqrt)      
      moreover have \<open>T \<noteq> {}\<close>
        unfolding T_def
        by blast
      moreover have \<open>bdd_above T\<close>
      proof(rule bdd_aboveI)
        fix x
        assume \<open>x \<in> T\<close>
        hence \<open>\<exists> R. finite R \<and> x = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R )\<close>
          unfolding T_def
          by blast
        then obtain R where \<open>finite R\<close> and \<open>x = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R )\<close>
          by blast
        from  \<open>finite R\<close>
        have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) \<le>  (ell2_norm \<psi>)^2\<close>
          by (simp add: \<open>\<And>R. finite R \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> (ell2_norm \<psi>)\<^sup>2\<close>)
        thus \<open>x \<le> (ell2_norm \<psi>)^2\<close>
          using  \<open>x = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R )\<close> by simp
      qed
      ultimately have \<open>sqrt (Sup T) = Sup (sqrt ` T)\<close>
        by (rule Topological_Spaces.continuous_at_Sup_mono)
      moreover have \<open>sqrt ` {\<Sum>i\<in>F. (cmod (\<phi> i))\<^sup>2 |F. F \<in> Collect finite}
             =  {sqrt (\<Sum>i\<in>F. (cmod (\<phi> i))\<^sup>2) |F. F \<in> Collect finite}\<close>
        by auto
      ultimately show ?thesis 
        unfolding T_def
        by simp
    qed
    ultimately have \<open>sqrt ( Sup { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} } ) \<le> ell2_norm \<psi>\<close>
      by simp
    moreover have \<open>ell2_norm \<phi> = sqrt ( Sup { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} } )\<close>
      unfolding ell2_norm_def
      by (metis Setcompr_eq_image)
    ultimately have \<open>ell2_norm \<phi> \<le> ell2_norm \<psi>\<close>
      by simp
    thus ?thesis
      unfolding C0_def \<phi>_def by simp
  qed

  hence bounded_C1: "\<exists>K. \<forall>x. norm (C1 x) \<le> norm x * K"
    apply transfer apply (rule exI[of _ 1]) by auto

  have "bounded_clinear C1"
    using \<open>clinear C1\<close> bounded_C1
    using add bounded_clinear_intro scaleC by blast

  define C where "C = CBlinfun C1"
  have [transfer_rule]: "pcr_cblinfun (=) (=) C1 C"
    unfolding C_def unfolding cblinfun.pcr_cr_eq cr_cblinfun_def
    apply (subst CBlinfun_inverse)
    using \<open>bounded_clinear C1\<close> by auto

  have C1_ket: "C1 (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    apply (transfer fixing: \<pi> x) unfolding C0_def
    apply (rule ext, rename_tac b)
    apply (case_tac "inv_map \<pi> b"; cases "\<pi> x")
       apply auto
       apply (metis inv_map_def option.simps(3) range_eqI)
      apply (metis f_inv_into_f inv_map_def option.distinct(1) option.sel)
     apply (metis f_inv_into_f inv_map_def option.sel option.simps(3))
    by (metis (no_types, lifting) assms f_inv_into_f inj_map_def inv_map_def option.sel option.simps(3))

  have "C *\<^sub>V ket x = (case \<pi> x of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)" for x
    using ket.transfer[transfer_rule del] zero_ell2.transfer[transfer_rule del] 
    apply (tactic \<open>all_tac\<close>)
    apply (transfer fixing: \<pi>)
    by (fact C1_ket)

  thus "classical_operator_exists \<pi>"
    by (rule classical_operator_existsI[of C])
qed

lemma classical_operator_exists_finite[simp]: "classical_operator_exists (\<pi> :: _::finite \<Rightarrow> _)"
  unfolding classical_operator_exists_def
  apply (rule cblinfun_extension_exists_finite_dim)
  using cindependent_ket apply blast
  using finite_class.finite_UNIV finite_imageI closed_cspan_range_ket closure_finite_cspan by blast

lemma classical_operator_ket:
  assumes "classical_operator_exists \<pi>"
  shows "(classical_operator \<pi>) *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  unfolding classical_operator_def 
  using f_inv_into_f ket_injective rangeI
  by (metis assms cblinfun_extension_apply classical_operator_exists_def)

lemma classical_operator_ket_finite:
  "(classical_operator \<pi>) *\<^sub>V (ket (x::'a::finite)) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  by (rule classical_operator_ket, simp)

lemma classical_operator_adjoint[simp]:
  fixes \<pi> :: "'a \<Rightarrow> 'b option"
  assumes a1: "inj_map \<pi>"
  shows  "(classical_operator \<pi>)* = classical_operator (inv_map \<pi>)"
proof-
  define F where "F = classical_operator (inv_map \<pi>)"
  define G where "G = classical_operator \<pi>"
  have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>" for i j
  proof-
    have w1: "(classical_operator (inv_map \<pi>)) *\<^sub>V (ket i)
     = (case inv_map \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      by (simp add: classical_operator_ket classical_operator_exists_inj)
    have w2: "(classical_operator \<pi>) *\<^sub>V (ket j)
     = (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      by (simp add: assms classical_operator_ket classical_operator_exists_inj)
    have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>classical_operator (inv_map \<pi>) *\<^sub>V ket i, ket j\<rangle>"
      unfolding F_def by blast
    also have "\<dots> = \<langle>(case inv_map \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0), ket j\<rangle>"
      using w1 by simp
    also have "\<dots> = \<langle>ket i, (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)\<rangle>"
    proof(induction "inv_map \<pi> i")
      case None
      hence pi1: "None = inv_map \<pi> i".
      show ?case 
      proof (induction "\<pi> j")
        case None
        thus ?case
          using pi1 by auto
      next
        case (Some c)
        have "c \<noteq> i"
        proof(rule classical)
          assume "\<not>(c \<noteq> i)"
          hence "c = i"
            by blast
          hence "inv_map \<pi> c = inv_map \<pi> i"
            by simp
          hence "inv_map \<pi> c = None"
            by (simp add: pi1)
          moreover have "inv_map \<pi> c = Some j"
            using Some.hyps unfolding inv_map_def
            apply auto
            by (metis a1 f_inv_into_f inj_map_def option.distinct(1) rangeI)
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (metis None.hyps Some.hyps cinner_zero_left orthogonal_ket option.simps(4) 
              option.simps(5)) 
      qed       
    next
      case (Some d)
      hence s1: "Some d = inv_map \<pi> i".
      show "\<langle>case inv_map \<pi> i of 
            None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case \<pi> j of 
            None \<Rightarrow> 0 
        | Some a \<Rightarrow> ket a\<rangle>" 
      proof(induction "\<pi> j")
        case None
        have "d \<noteq> j"
        proof(rule classical)
          assume "\<not>(d \<noteq> j)"
          hence "d = j"
            by blast
          hence "\<pi> d = \<pi> j"
            by simp
          hence "\<pi> d = None"
            by (simp add: None.hyps)
          moreover have "\<pi> d = Some i"
            using Some.hyps unfolding inv_map_def
            apply auto
            by (metis f_inv_into_f option.distinct(1) option.inject)
          ultimately show ?thesis 
            by simp
        qed
        thus ?case
          by (metis None.hyps Some.hyps cinner_zero_right orthogonal_ket option.case_eq_if 
              option.simps(5)) 
      next
        case (Some c)
        hence s2: "\<pi> j = Some c" by simp
        have "\<langle>ket d, ket j\<rangle> = \<langle>ket i, ket c\<rangle>"
        proof(cases "\<pi> j = Some i")
          case True
          hence ij: "Some j = inv_map \<pi> i"
            unfolding inv_map_def apply auto
             apply (metis a1 f_inv_into_f inj_map_def option.discI range_eqI)
            by (metis range_eqI)
          have "i = c"
            using True s2 by auto
          moreover have "j = d"
            by (metis option.inject s1 ij)
          ultimately show ?thesis
            by (simp add: cinner_ket_same) 
        next
          case False
          moreover have "\<pi> d = Some i"
            using s1 unfolding inv_map_def
            by (metis f_inv_into_f option.distinct(1) option.inject)            
          ultimately have "j \<noteq> d"
            by auto            
          moreover have "i \<noteq> c"
            using False s2 by auto            
          ultimately show ?thesis
            by (metis orthogonal_ket) 
        qed
        hence "\<langle>case Some d of None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case Some c of None \<Rightarrow> 0 | Some a \<Rightarrow> ket a\<rangle>"
          by simp          
        thus "\<langle>case inv_map \<pi> i of None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case \<pi> j of None \<Rightarrow> 0 | Some a \<Rightarrow> ket a\<rangle>"
          by (simp add: Some.hyps s1)          
      qed
    qed
    also have "\<dots> = \<langle>ket i, classical_operator \<pi> *\<^sub>V ket j\<rangle>"
      by (simp add: w2)
    also have "\<dots> = \<langle>ket i, G *\<^sub>V ket j\<rangle>"
      unfolding G_def by blast
    finally show ?thesis .
  qed
  hence "G* = F"
    using cinner_ket_adjointI
    by auto
  thus ?thesis unfolding G_def F_def .
qed

lemma
  fixes \<pi>::"'b \<Rightarrow> 'c option" and \<rho>::"'a \<Rightarrow> 'b option"
  assumes "classical_operator_exists \<pi>"
  assumes "classical_operator_exists \<rho>"
  shows classical_operator_exists_comp[simp]: "classical_operator_exists (\<pi> \<circ>\<^sub>m \<rho>)"
    and classical_operator_mult[simp]: "classical_operator \<pi> o\<^sub>C\<^sub>L classical_operator \<rho> = classical_operator (\<pi> \<circ>\<^sub>m \<rho>)"
proof -
  define C\<pi> C\<rho> C\<pi>\<rho> where "C\<pi> = classical_operator \<pi>" and "C\<rho> = classical_operator \<rho>" 
    and "C\<pi>\<rho> = classical_operator (\<pi> \<circ>\<^sub>m \<rho>)"
  have C\<pi>x: "C\<pi> *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<pi>_def using \<open>classical_operator_exists \<pi>\<close> by (rule classical_operator_ket)
  have C\<rho>x: "C\<rho> *\<^sub>V (ket x) = (case \<rho> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<rho>_def using \<open>classical_operator_exists \<rho>\<close> by (rule classical_operator_ket)
  have C\<pi>\<rho>x': "(C\<pi> o\<^sub>C\<^sub>L C\<rho>) *\<^sub>V (ket x) = (case (\<pi> \<circ>\<^sub>m \<rho>) x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    apply (simp add: scaleC_cblinfun.rep_eq C\<rho>x)
    apply (cases "\<rho> x")
    by (auto simp: C\<pi>x)
  thus \<open>classical_operator_exists (\<pi> \<circ>\<^sub>m \<rho>)\<close>
    by (rule classical_operator_existsI)
  hence "C\<pi>\<rho> *\<^sub>V (ket x) = (case (\<pi> \<circ>\<^sub>m \<rho>) x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<pi>\<rho>_def
    by (rule classical_operator_ket)
  with C\<pi>\<rho>x' have "(C\<pi> o\<^sub>C\<^sub>L C\<rho>) *\<^sub>V (ket x) = C\<pi>\<rho> *\<^sub>V (ket x)" for x
    by simp
  thus "C\<pi> o\<^sub>C\<^sub>L C\<rho> = C\<pi>\<rho>"
    by (simp add: equal_ket)
qed

lemma classical_operator_Some[simp]: "classical_operator (Some::'a\<Rightarrow>_) = id_cblinfun"
proof-
  have "(classical_operator Some) *\<^sub>V (ket i)  = id_cblinfun *\<^sub>V (ket i)"
    for i::'a
    apply (subst classical_operator_ket)
     apply (rule classical_operator_exists_inj)
    by auto
  thus ?thesis
    using equal_ket[where A = "classical_operator (Some::'a \<Rightarrow> _ option)"
        and B = "id_cblinfun::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _"]
    by blast
qed

lemma isometry_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  assumes a1: "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have b0: "inj_map (Some \<circ> \<pi>)"
    by (simp add: a1)
  have b0': "inj_map (inv_map (Some \<circ> \<pi>))"
    by simp
  have b1: "inv_map (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_map_def o_def 
    using assms unfolding inj_def inv_def by auto
  have b3: "classical_operator (inv_map (Some \<circ> \<pi>)) o\<^sub>C\<^sub>L
            classical_operator (Some \<circ> \<pi>) = classical_operator (inv_map (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>))"
    by (metis b0 b0' b1 classical_operator_Some classical_operator_exists_inj 
        classical_operator_mult)
  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint)
    using b0 by (auto simp add: b1 b3)
qed

lemma unitary_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  assumes a1: "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "inj \<pi>"
    using a1 bij_betw_imp_inj_on by auto
  hence "isometry (classical_operator (Some o \<pi>))"
    by simp
  hence "classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = id_cblinfun"
    unfolding isometry_def by simp
  thus \<open>classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = id_cblinfun\<close>
    by simp 
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_map (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_map_def o_def map_comp_def
    unfolding inv_def apply auto
     apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    using bij_def image_iff range_eqI
    by (metis a1)
  have "classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>)*
      = classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (inv_map (Some \<circ> \<pi>))"
    by (simp add: \<open>inj \<pi>\<close>)
  also have "\<dots> = classical_operator ((Some \<circ> \<pi>) \<circ>\<^sub>m (inv_map (Some \<circ> \<pi>)))"
    by (simp add: \<open>inj \<pi>\<close> classical_operator_exists_inj)
  also have "\<dots> = classical_operator (Some::'b\<Rightarrow>_)"
    using comp
    by simp 
  also have "\<dots> = (id_cblinfun:: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L _)"
    by simp
  finally show "classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>)* = id_cblinfun".
qed



unbundle no_cblinfun_notation

end
