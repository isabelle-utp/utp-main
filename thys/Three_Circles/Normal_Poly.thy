section \<open>Normal Polynomials\<close>

theory Normal_Poly
  imports "RRI_Misc"
begin

text \<open>
Here we define normal polynomials as defined in
  Basu, S., Pollack, R., Roy, M.-F.: Algorithms in Real Algebraic Geometry. 
  Springer Berlin Heidelberg, Berlin, Heidelberg (2016).
\<close>

definition normal_poly :: "('a::{comm_ring_1,ord}) poly \<Rightarrow> bool" where
"normal_poly p \<equiv>
  (p \<noteq> 0) \<and>
  (\<forall> i. 0 \<le> coeff p i) \<and>
  (\<forall> i. coeff p i * coeff p (i+2) \<le> (coeff p (i+1))^2) \<and>
  (\<forall> i j k. i \<le> j \<longrightarrow> j \<le> k \<longrightarrow> 0 < coeff p i 
      \<longrightarrow> 0 < coeff p k \<longrightarrow> 0 < coeff p j)"

lemma normal_non_zero: "normal_poly p \<Longrightarrow> p \<noteq> 0" 
  using normal_poly_def by blast

lemma normal_coeff_nonneg: "normal_poly p \<Longrightarrow> 0 \<le> coeff p i" 
  using normal_poly_def by metis

lemma normal_poly_coeff_mult: 
    "normal_poly p \<Longrightarrow> coeff p i * coeff p (i+2) \<le> (coeff p (i+1))^2" 
  using normal_poly_def by blast

lemma normal_poly_pos_interval: 
    "normal_poly p \<Longrightarrow> i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> 0 < coeff p i \<Longrightarrow> 0 < coeff p k 
      \<Longrightarrow> 0 < coeff p j" 
  using normal_poly_def by blast

lemma normal_polyI:
  assumes "(p \<noteq> 0)"
      and "(\<And> i. 0 \<le> coeff p i)"
      and "(\<And> i. coeff p i * coeff p (i+2) \<le> (coeff p (i+1))^2)"
      and "(\<And> i j k. i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> 0 < coeff p i \<Longrightarrow> 0 < coeff p k \<Longrightarrow> 0 < coeff p j)"
    shows "normal_poly p"
  using assms by (force simp: normal_poly_def)

lemma linear_normal_iff: 
  fixes x::real 
  shows "normal_poly [:-x, 1:] \<longleftrightarrow> x \<le> 0"
proof
  assume "normal_poly [:-x, 1:]"
  thus "x \<le> 0" using normal_coeff_nonneg[of "[:-x, 1:]" 0] by auto
next
  assume "x \<le> 0"
  then have "0 \<le> coeff [:- x, 1:] i" for i
    by (cases i) (simp_all add: pCons_one)
  moreover have "0 < coeff [:- x, 1:] j"
    if "i \<le> j" "j \<le> k" "0 < coeff [:- x, 1:] i" 
        "0 < coeff [:- x, 1:] k" for i j k
    apply (cases "k=0 \<or> i=0")
    subgoal using that 
      by (smt (z3) bot_nat_0.extremum_uniqueI degree_pCons_eq_if 
          le_antisym le_degree not_less_eq_eq)
    subgoal using that 
      by (smt (z3) One_nat_def degree_pCons_eq_if le_degree less_one
          not_le one_neq_zero pCons_one verit_la_disequality)
    done
  ultimately show "normal_poly [:-x, 1:]"
    unfolding normal_poly_def by auto
qed

lemma quadratic_normal_iff: 
  fixes z::complex 
  shows "normal_poly [:(cmod z)\<^sup>2, -2*Re z, 1:] 
          \<longleftrightarrow> Re z \<le> 0 \<and> 4*(Re z)^2 \<ge> (cmod z)^2"
proof
  assume "normal_poly [:(cmod z)\<^sup>2, - 2 * Re z, 1:]"
  hence "-2*Re z \<ge> 0 \<and> (cmod z)^2 \<ge> 0 \<and> (-2*Re z)^2 \<ge> (cmod z)^2"
    using normal_coeff_nonneg[of _ 1] normal_poly_coeff_mult[of _ 0] 
    by fastforce
  thus "Re z \<le> 0 \<and> 4*(Re z)^2 \<ge> (cmod z)^2"
    by auto
next
  assume asm:"Re z \<le> 0 \<and> 4*(Re z)^2 \<ge> (cmod z)^2"
  define P where "P=[:(cmod z)\<^sup>2, - 2 * Re z, 1:]"

  have "0 \<le> coeff P i" for i 
    unfolding P_def using asm
    apply (cases "i=0\<or>i=1\<or>i=2")
    by (auto simp:numeral_2_eq_2 coeff_eq_0)
  moreover have "coeff P i * coeff P (i + 2) \<le> (coeff P (i + 1))\<^sup>2" for i
    apply (cases "i=0\<or>i=1\<or>i=2")
    using asm 
    unfolding P_def by (auto simp:coeff_eq_0)
  moreover have "0 < coeff P j"
    if "0 < coeff P k" "0 < coeff P i" "j \<le> k" "i \<le> j"
    for i j k
    using that unfolding P_def 
    apply (cases "k=0 \<or> k=1 \<or> k=2")
    subgoal using asm
      by (smt (z3) One_nat_def Suc_1 bot_nat_0.extremum_uniqueI 
          coeff_pCons_0 coeff_pCons_Suc le_Suc_eq 
          zero_less_power2)
    subgoal by (auto simp:coeff_eq_0)
    done
  moreover have "P\<noteq>0" unfolding P_def by auto
  ultimately show "normal_poly P"
    unfolding normal_poly_def by blast
qed

lemma normal_of_no_zero_root: 
  fixes f::"real poly" 
  assumes hzero: "poly f 0 \<noteq> 0" and hdeg: "i \<le> degree f" 
    and hnorm: "normal_poly f"
  shows "0 < coeff f i"
proof -
  have "coeff f 0 > 0" using hzero normal_coeff_nonneg[OF hnorm]
    by (metis eq_iff not_le_imp_less poly_0_coeff_0)
  moreover have "coeff f (degree f) > 0" using normal_coeff_nonneg[OF hnorm] normal_non_zero[OF hnorm]
    by (meson dual_order.irrefl eq_iff eq_zero_or_degree_less not_le_imp_less)
  moreover have "0 \<le> i" by simp
  ultimately show "0 < coeff f i" using hdeg normal_poly_pos_interval[OF hnorm] by blast
qed

lemma normal_divide_x: 
  fixes f::"real poly" 
  assumes hnorm: "normal_poly (f*[:0,1:])"
  shows "normal_poly f"
proof (rule normal_polyI)
  show "f \<noteq> 0"
    using normal_non_zero[OF hnorm] by auto
next
  fix i
  show "0 \<le> coeff f i"
    using normal_coeff_nonneg[OF hnorm, of "Suc i"] by (simp add: coeff_pCons)
next
  fix i
  show "coeff f i * coeff f (i + 2) \<le> (coeff f (i + 1))\<^sup>2"
    using normal_poly_coeff_mult[OF hnorm, of "Suc i"] by (simp add: coeff_pCons)
next
  fix i j k
  show "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> 0 < coeff f i \<Longrightarrow> 0 < coeff f k \<Longrightarrow> 0 < coeff f j"
    using normal_poly_pos_interval[of _ "Suc i" "Suc j" "Suc k", OF hnorm]
    by (simp add: coeff_pCons)
qed

lemma normal_mult_x: 
  fixes f::"real poly" 
  assumes hnorm: "normal_poly f"
  shows "normal_poly (f * [:0, 1:])"
proof (rule normal_polyI)
  show "f * [:0, 1:] \<noteq> 0"
    using normal_non_zero[OF hnorm] by auto
next
  fix i
  show "0 \<le> coeff (f * [:0, 1:]) i"
    using normal_coeff_nonneg[OF hnorm, of "i-1"] by (cases i, auto simp: coeff_pCons)
next
  fix i
  show "coeff (f * [:0, 1:]) i * coeff (f * [:0, 1:]) (i + 2) \<le> (coeff (f * [:0, 1:]) (i + 1))\<^sup>2"
    using normal_poly_coeff_mult[OF hnorm, of "i-1"] by (cases i, auto simp: coeff_pCons)
next
  fix i j k
  show "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> 0 < coeff (f * [:0, 1:]) i \<Longrightarrow> 0 < coeff (f * [:0, 1:]) k \<Longrightarrow> 0 < coeff (f * [:0, 1:]) j"
    using normal_poly_pos_interval[of _ "i-1" "j-1" "k-1", OF hnorm]
    apply (cases i, force)
    apply (cases j, force)
    apply (cases k, force)
    by (auto simp: coeff_pCons)
qed

lemma normal_poly_general_coeff_mult: 
  fixes f::"real poly" 
  assumes "normal_poly f" and "h \<le> j"
  shows "coeff f (h+1) * coeff f (j+1) \<ge> coeff f h * coeff f (j+2)"
using assms proof (induction j)
  case 0
  then show ?case
    using normal_poly_coeff_mult by (auto simp: power2_eq_square)[1]
next
  case (Suc j)
  then show ?case
  proof (cases "h = Suc j")
    assume "h = Suc j" "normal_poly f"
    thus ?thesis
      using normal_poly_coeff_mult by (auto simp: power2_eq_square)
  next
    assume "(normal_poly f \<Longrightarrow>
       h \<le> j \<Longrightarrow> coeff f h * coeff f (j + 2) \<le> coeff f (h + 1) * coeff f (j + 1))"
      "normal_poly f" and h: "h \<le> Suc j" "h \<noteq> Suc j"
    hence IH: "coeff f h * coeff f (j + 2) \<le> coeff f (h + 1) * coeff f (j + 1)"
      by linarith
    show ?thesis
    proof (cases "coeff f (Suc j + 1) = 0", cases "coeff f (Suc j + 2) = 0")
      show "coeff f (Suc j + 1) = 0 \<Longrightarrow> coeff f (Suc j + 2) = 0 \<Longrightarrow>
        coeff f h * coeff f (Suc j + 2) \<le> coeff f (h + 1) * coeff f (Suc j + 1)"
        by (metis assms(1) mult_zero_right normal_coeff_nonneg)
    next
      assume 1: "coeff f (Suc j + 1) = 0" "coeff f (Suc j + 2) \<noteq> 0"
      hence "coeff f (Suc j + 2) > 0" "\<not>coeff f (Suc j + 1) > 0" 
        using normal_coeff_nonneg[of f "Suc j + 2"] assms(1) by auto
      hence "coeff f h > 0 \<Longrightarrow> False"
        using normal_poly_pos_interval[of f h "Suc j + 1" "Suc j + 2"] assms(1) h by force
      hence "coeff f h = 0"
        using normal_coeff_nonneg[OF assms(1)] less_eq_real_def by auto
      thus "coeff f h * coeff f (Suc j + 2) \<le> coeff f (h + 1) * coeff f (Suc j + 1)"
        using 1 by fastforce
    next
      assume 1: "coeff f (Suc j + 1) \<noteq> 0"
      show "coeff f h * coeff f (Suc j + 2) \<le> coeff f (h + 1) * coeff f (Suc j + 1)"
      proof (cases "coeff f (Suc j) = 0")
        assume 2: "coeff f (Suc j) = 0"
        hence "coeff f (Suc j + 1) > 0" "\<not>coeff f (Suc j) > 0" 
          using normal_coeff_nonneg[of f "Suc j + 1"] assms(1) 1 by auto
        hence "coeff f h > 0 \<Longrightarrow> False"
          using normal_poly_pos_interval[of f h "Suc j" "Suc j + 1"] assms(1) h by force
        hence "coeff f h = 0"
          using normal_coeff_nonneg[OF assms(1)] less_eq_real_def by auto
        thus "coeff f h * coeff f (Suc j + 2) \<le> coeff f (h + 1) * coeff f (Suc j + 1)"
          by (simp add: assms(1) normal_coeff_nonneg)
      next
        assume 2: "coeff f (Suc j) \<noteq> 0"
        from normal_poly_coeff_mult[OF assms(1), of "Suc j"] normal_coeff_nonneg[OF assms(1), of "Suc j"]
          normal_coeff_nonneg[OF assms(1), of "Suc (Suc j)"] 1 2 
        have 3: "coeff f (Suc j + 1) / coeff f (Suc j) \<ge> coeff f (Suc j + 2) / coeff f (Suc j + 1)"
          by (auto simp: power2_eq_square divide_simps algebra_simps)
        have "(coeff f h * coeff f (j + 2)) * (coeff f (Suc j + 2) / coeff f (Suc j + 1)) \<le> (coeff f (h + 1) * coeff f (j + 1)) * (coeff f (Suc j + 1) / coeff f (Suc j))"
          apply (rule mult_mono[OF IH])
          using 3 by (simp_all add: assms(1) normal_coeff_nonneg)
        thus "coeff f h * coeff f (Suc j + 2) \<le> coeff f (h + 1) * coeff f (Suc j + 1)"
          using 1 2 by fastforce
      qed
    qed
  qed
qed

lemma normal_mult: 
  fixes f g::"real poly"
  assumes hf: "normal_poly f" and hg: "normal_poly g"
  defines "df \<equiv> degree f" and "dg \<equiv> degree g"
  shows "normal_poly (f*g)"
using df_def hf proof (induction df arbitrary: f)
text \<open>We shall first show that without loss of generality we may assume \<open>poly f 0 \<noteq> 0\<close>,
      this is done by induction on the degree, if 0 is a root then we derive the result from \<open>f/[:0,1:]\<close>.\<close>
  fix f::"real poly" fix i::nat
  assume "0 = degree f" and hf: "normal_poly f"
  then obtain a where "f = [:a:]" using degree_0_iff by auto
  then show "normal_poly (f*g)"
    apply (subst normal_polyI)
    subgoal using normal_non_zero[OF hf] normal_non_zero[OF hg] by auto
    subgoal 
      using normal_coeff_nonneg[of _ 0, OF hf] normal_coeff_nonneg[OF hg] 
      by simp
    subgoal 
      using normal_coeff_nonneg[of _ 0, OF hf] normal_poly_coeff_mult[OF hg] 
      by (auto simp: algebra_simps power2_eq_square mult_left_mono)[1]
    subgoal 
      using normal_non_zero[OF hf] normal_coeff_nonneg[of _ 0, OF hf] normal_poly_pos_interval[OF hg]
      by (simp add: zero_less_mult_iff)
    subgoal by simp
    done
next
  case (Suc df)
  then show ?case
  proof (cases "poly f 0 = 0")
    assume "poly f 0 = 0" and hf:"normal_poly f"
    moreover then obtain f' where hdiv: "f = f'*[:0,1:]"
      by (smt (verit) dvdE mult.commute poly_eq_0_iff_dvd) 
    ultimately have hf': "normal_poly f'" using normal_divide_x by blast
    assume "Suc df = degree f"
    hence "degree f' = df" using hdiv normal_non_zero[OF hf'] by (auto simp: degree_mult_eq)
    moreover assume "\<And>f. df = degree f \<Longrightarrow> normal_poly f \<Longrightarrow> normal_poly (f * g)"
    ultimately have "normal_poly (f'*g)" using hf' by blast
    thus "normal_poly (f*g)" using hdiv normal_mult_x by fastforce
  next
    assume hf: "normal_poly f" and hf0: "poly f 0 \<noteq> 0"
    define dg where "dg \<equiv> degree g"
    show "normal_poly (f * g)"
    using dg_def hg proof (induction dg arbitrary: g)
      text \<open>Similarly we may assume \<open>poly g 0 \<noteq> 0\<close>.\<close>
      fix g::"real poly" fix i::nat
      assume "0 = degree g" and hg: "normal_poly g"
      then obtain a where "g = [:a:]" using degree_0_iff by auto
      then show "normal_poly (f*g)"
        apply (subst normal_polyI)
        subgoal 
          using normal_non_zero[OF hg] normal_non_zero[OF hf] by auto
        subgoal 
          using normal_coeff_nonneg[of _ 0, OF hg] normal_coeff_nonneg[OF hf] 
          by simp
        subgoal 
          using normal_coeff_nonneg[of _ 0, OF hg] normal_poly_coeff_mult[OF hf] 
          by (auto simp: algebra_simps power2_eq_square mult_left_mono)
        subgoal 
          using normal_non_zero[OF hf] normal_coeff_nonneg[of _ 0, OF hg] 
            normal_poly_pos_interval[OF hf]
          by (simp add: zero_less_mult_iff)
        by simp
    next
      case (Suc dg)
      then show ?case
      proof (cases "poly g 0 = 0")
        assume "poly g 0 = 0" and hg:"normal_poly g"
        moreover then obtain g' where hdiv: "g = g'*[:0,1:]"
          by (smt (verit) dvdE mult.commute poly_eq_0_iff_dvd) 
        ultimately have hg': "normal_poly g'" using normal_divide_x by blast
        assume "Suc dg = degree g"
        hence "degree g' = dg" using hdiv normal_non_zero[OF hg'] by (auto simp: degree_mult_eq)
        moreover assume "\<And>g. dg = degree g \<Longrightarrow> normal_poly g \<Longrightarrow> normal_poly (f * g)"
        ultimately have "normal_poly (f*g')" using hg' by blast
        thus "normal_poly (f*g)" using hdiv normal_mult_x by fastforce
      next
        text \<open>It now remains to show that $(fg)_i \geq 0$. This follows by decomposing $\{(h, j) \in
              \mathbf{Z}^2 | h > j\} = \{(h, j) \in \mathbf{Z}^2 | h \leq j\} \cup \{(h, h - 1) \in 
              \mathbf{Z}^2 | h \in \mathbf{Z}\}$.
              Note in order to avoid working with infinite sums over integers all these sets are
              bounded, which adds some complexity compared to the proof of lemma 2.55 in
              Basu, S., Pollack, R., Roy, M.-F.: Algorithms in Real Algebraic Geometry.
              Springer Berlin Heidelberg, Berlin, Heidelberg (2016).\<close>
        assume hg0: "poly g 0 \<noteq> 0" and hg: "normal_poly g"
        have "f * g \<noteq> 0" using hf hg by (simp add: normal_non_zero Suc.prems)
        moreover have "\<And>i. coeff (f*g) i \<ge> 0"
          apply (subst coeff_mult, rule sum_nonneg, rule mult_nonneg_nonneg)
          using normal_coeff_nonneg[OF hf] normal_coeff_nonneg[OF hg] by auto
        moreover have "
          coeff (f*g) i * coeff (f*g) (i+2) \<le> (coeff (f*g) (i+1))^2" for i
        proof -

          text \<open>$(fg)_{i+1}^2 - (fg)_i(fg)_{i+2} = \left(\sum_x f_xg_{i+1-x}\right)^2 - 
                \left(\sum_x f_xg_{i+2-x}\right)\left(\sum_x f_xg_{i-x}\right)$\<close>
          have "(coeff (f*g) (i+1))^2 - coeff (f*g) i * coeff (f*g) (i+2) = 
              (\<Sum>x\<le>i+1. coeff f x * coeff g (i + 1 - x)) *
              (\<Sum>x\<le>i+1. coeff f x * coeff g (i + 1 - x)) -
              (\<Sum>x\<le>i+2. coeff f x * coeff g (i + 2 - x)) *
              (\<Sum>x\<le>i. coeff f x * coeff g (i - x))"
            by (auto simp: coeff_mult power2_eq_square algebra_simps)
          
          text \<open>$\dots = \sum_{x, y} f_xg_{i+1-x}f_yg_{i+1-y} - \sum_{x, y} f_xg_{i+2-x}f_yg_{i-y}$\<close>
          also have "... =
              (\<Sum>x\<le>i+1. \<Sum>y\<le>i+1. coeff f x * coeff g (i + 1 - x) *
                                  coeff f y * coeff g (i + 1 - y)) -
              (\<Sum>x\<le>i+2. \<Sum>y\<le>i. coeff f x * coeff g (i + 2 - x) *
                                coeff f y * coeff g (i - y))"
            by (subst sum_product, subst sum_product, auto simp: algebra_simps)

          text \<open>$\dots = \sum_{h \leq j} f_hg_{i+1-h}f_jg_{i+1-j} + \sum_{h>j} f_hg_{i+1-h}f_jg_{i+1-j}
                       - \sum_{h \leq j} f_hg_{i+2-h}f_jg_{i-j} - \sum_{h>j} f_hg_{i+2-h}f_jg_{i-j}$\<close>
          also have "... =
              (\<Sum>(h, j)\<in>{(h, j). i+1 \<ge> j \<and> j \<ge> h}. 
                coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j)) +
              (\<Sum>(h, j)\<in>{(h, j). i+1 \<ge> h \<and> h > j}. 
                coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j)) -
             ((\<Sum>(h, j)\<in>{(h, j). i \<ge> j \<and> j \<ge> h}. 
                coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j)) +
              (\<Sum>(h, j)\<in>{(h, j). i + 2 \<ge> h \<and> h > j \<and> i \<ge> j}.
                coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j)))"
          proof -
            have "(\<Sum>x\<le>i + 1. \<Sum>y\<le>i + 1. coeff f x * coeff g (i + 1 - x) * coeff f y * coeff g (i + 1 - y)) =
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j}.
                 coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j)) +
              (\<Sum>(h, j)\<in>{(h, j). h \<le> i + 1 \<and> j < h}.
                 coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j))"
            proof (subst sum.union_disjoint[symmetric])
              have H:"{(h, j). j \<le> i + 1 \<and> h \<le> j} \<subseteq> {..i+1} \<times> {..i+1}"
                     "{(h, j). h \<le> i + 1 \<and> j < h} \<subseteq> {..i+1} \<times> {..i+1}"
                     "finite ({..i+1} \<times> {..i+1})"
                by (fastforce, fastforce, fastforce)
              show "finite {(h, j). j \<le> i + 1 \<and> h \<le> j}"
                apply (rule finite_subset) using H by (blast, blast)
              show "finite {(h, j). h \<le> i + 1 \<and> j < h}"
                apply (rule finite_subset) using H by (blast, blast)
              show "{(h, j). j \<le> i + 1 \<and> h \<le> j} \<inter> {(h, j). h \<le> i + 1 \<and> j < h} = {}"
                by fastforce
              show "(\<Sum>x\<le>i + 1. \<Sum>y\<le>i + 1. coeff f x * coeff g (i + 1 - x) * coeff f y * coeff g (i + 1 - y)) =
                  (\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j} \<union> {(h, j). h \<le> i + 1 \<and> j < h}.
                    coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j))"
                apply (subst sum.cartesian_product, rule sum.cong)
                apply force by blast
            qed
            moreover have "(\<Sum>x\<le>i + 2. \<Sum>y\<le>i. coeff f x * coeff g (i + 2 - x) * coeff f y * coeff g (i - y)) =
               (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                  coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j)) +
               (\<Sum>(h, j)\<in>{(h, j). i + 2 \<ge> h \<and> h > j \<and> i \<ge> j}.
                  coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j))"
            proof (subst sum.union_disjoint[symmetric])
              have H:"{(h, j). j \<le> i \<and> h \<le> j} \<subseteq> {..i+2} \<times> {..i}"
                     "{(h, j). i + 2 \<ge> h \<and> h > j \<and> i \<ge> j} \<subseteq> {..i+2} \<times> {..i}"
                     "finite ({..i+2} \<times> {..i})"
                by (fastforce, fastforce, fastforce)
              show "finite {(h, j). j \<le> i \<and> h \<le> j}"
                apply (rule finite_subset) using H by (blast, blast)
              show "finite {(h, j). i + 2 \<ge> h \<and> h > j \<and> i \<ge> j}"
                apply (rule finite_subset) using H by (blast, blast)
              show "{(h, j). j \<le> i \<and> h \<le> j} \<inter> {(h, j). i + 2 \<ge> h \<and> h > j \<and> i \<ge> j} = {}"
                by fastforce
              show "(\<Sum>x\<le>i + 2. \<Sum>y\<le>i. coeff f x * coeff g (i + 2 - x) * coeff f y * coeff g (i - y)) =
                  (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j} \<union> {(h, j). i + 2 \<ge> h \<and> h > j \<and> i \<ge> j}.
                     coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j))"
                apply (subst sum.cartesian_product, rule sum.cong)
                apply force by blast
            qed
            ultimately show ?thesis by presburger
          qed

          text \<open>$\dots = \sum_{h \leq j} f_hg_{i+1-h}f_jg_{i+1-j} + \sum_{h \leq j} f_{j+1}g_{i-j}f_{h-2}g_{i+2-h} 
                       + \sum_h f_hg_{i+1-h}f_{h-1}g_{i+2-h} - \sum_{h \leq j} f_hg_{i+2-h}f_jg_{i-j}
                       - \sum_{h \leq j} f_{j+1}g_{i+1-j}f_{h-2}g_{i+1-h} - \sum_h f_hg_{i+2-h}f_{h-1}g_{i+1-h}$\<close>
          also have "... =
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j}.
                 coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j)) +
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                 coeff f (j+1) * coeff g (i - j) * coeff f (h-1) * coeff g (i + 2 - h)) +
              (\<Sum>h\<in>{1..i+1}.
                 coeff f h * coeff g (i + 1 - h) * coeff f (h-1) * coeff g (i + 2 - h)) -
              ((\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                  coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j)) +
               (\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h}.
                  coeff f (j+1) * coeff g (i + 1 - j) * coeff f (h-1) * coeff g (i + 1 - h)) +
               (\<Sum>h\<in>{1..i+1}.
                  coeff f h * coeff g (i + 2 - h) * coeff f (h-1) * coeff g (i + 1 - h)))"
          proof -
            have "(\<Sum>(h, j)\<in>{(h, j). h \<le> i + 1 \<and> j < h}.
                   coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j)) = 
                  (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                   coeff f (j + 1) * coeff g (i - j) * coeff f (h - 1) * coeff g (i + 2 - h)) +
                  (\<Sum>h = 1..i + 1. coeff f h * coeff g (i + 1 - h) * coeff f (h - 1) * coeff g (i + 2 - h))"
            proof -
              have 1: "(\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                     coeff f (j + 1) * coeff g (i - j) * coeff f (h - 1) * coeff g (i + 2 - h)) =
                    (\<Sum>(h, j)\<in>{(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}.
                     coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j))"
              proof (rule sum.reindex_cong)
                show "{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h} = (\<lambda>(h, j). (j+1, h-1)) ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}"
                proof
                  show "(\<lambda>(h, j). (j + 1, h - 1)) ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1} \<subseteq> {(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}"
                    by fastforce
                  show "{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h} \<subseteq> (\<lambda>(h, j). (j + 1, h - 1)) ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}"
                  proof
                    fix x
                    assume "x \<in> {(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}"
                    then obtain h j where "x = (h, j)" "j \<le> i" "h \<le> j" "0 < h" by blast
                    hence "j + 1 \<le> i + 1 \<and> h - 1 < j + 1 \<and> j + 1 \<noteq> h - 1 + 1 \<and> x = ((h - 1) + 1, (j + 1) - 1)"
                      by auto
                    thus "x \<in> (\<lambda>(h, j). (j + 1, h - 1)) ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}"
                      by (auto simp: image_iff)
                  qed
                qed
                show "inj_on (\<lambda>(h, j). (j + 1, h - 1)) {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}"
                proof
                  fix x y::"nat\<times>nat"
                  assume "x \<in> {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}" "y \<in> {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}"
                  thus "(case x of (h, j) \<Rightarrow> (j + 1, h - 1)) = (case y of (h, j) \<Rightarrow> (j + 1, h - 1)) \<Longrightarrow> x = y"
                    by auto
                qed
                show "\<And>x. x \<in> {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1} \<Longrightarrow>
                 (case case x of (h, j) \<Rightarrow> (j + 1, h - 1) of
                  (h, j) \<Rightarrow> coeff f (j + 1) * coeff g (i - j) * coeff f (h - 1) * coeff g (i + 2 - h)) =
                 (case x of (h, j) \<Rightarrow> coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j))"
                  by fastforce
              qed
              have 2: "(\<Sum>h = 1..i + 1. coeff f h * coeff g (i + 1 - h) * coeff f (h - 1) * coeff g (i + 2 - h)) =
                    (\<Sum>(h, j)\<in>{(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}.
                     coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j))"
              proof (rule sum.reindex_cong)
                show "{1..i + 1} = fst ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}"
                proof
                  show "{1..i + 1} \<subseteq> fst ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}"
                  proof
                    fix x
                    assume "x \<in> {1..i + 1}"
                    hence "x \<le> i + 1 \<and> x - 1 < x \<and> x = x - 1 + 1 \<and> x = fst (x, x-1)"
                      by auto
                    thus "x \<in> fst ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}"
                      by blast
                  qed
                  show "fst ` {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1} \<subseteq> {1..i + 1}"
                    by force
                qed
                show "inj_on fst {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}"
                proof
                  fix x y
                  assume "x \<in> {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}"
                         "y \<in> {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}"
                  hence "x = (fst x, fst x - 1)" "y = (fst y, fst y - 1)" "fst x > 0" "fst y > 0"
                    by auto
                  thus "fst x = fst y \<Longrightarrow> x = y" by presburger
                qed
                show "\<And>x. x \<in> {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1} \<Longrightarrow>
                   coeff f (fst x) * coeff g (i + 1 - fst x) * coeff f (fst x - 1) * coeff g (i + 2 - fst x) =
                   (case x of (h, j) \<Rightarrow> coeff f h * coeff g (i + 1 - h) * coeff f j * coeff g (i + 1 - j))"
                  by fastforce
              qed
              have H: "{(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1} \<subseteq> {0..i+1}\<times>{0..i+1}"
                      "{(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1} \<subseteq> {0..i+1}\<times>{0..i+1}"
                      "finite ({0..i+1}\<times>{0..i+1})"
                by (fastforce, fastforce, fastforce)
              have "finite {(h, j). h \<le> i + 1 \<and> j < h \<and> h \<noteq> j + 1}"
                   "finite {(h, j). h \<le> i + 1 \<and> j < h \<and> h = j + 1}"
                apply (rule finite_subset) using H apply (simp, simp)
                apply (rule finite_subset) using H apply (simp, simp)
                done
              thus ?thesis 
                apply (subst 1, subst 2, subst sum.union_disjoint[symmetric])
                   apply auto[3]
                apply (rule sum.cong)
                by auto
            qed
            moreover have "(\<Sum>(h, j)\<in>{(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i}.
                  coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j)) = 
               (\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h}.
                  coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) +
               (\<Sum>h = 1..i + 1. coeff f h * coeff g (i + 2 - h) * coeff f (h - 1) * coeff g (i + 1 - h))"
            proof -
              have 1: "(\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h}.
                     coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) =
                    (\<Sum>(h, j)\<in>{(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}.
                     coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j))"
              proof (rule sum.reindex_cong)
                show "{(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h} = (\<lambda>(h, j). (j+1, h-1)) ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}"
                proof
                  show "(\<lambda>(h, j). (j + 1, h - 1)) ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1} \<subseteq> {(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h}"
                    by fastforce
                  show "{(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h} \<subseteq> (\<lambda>(h, j). (j + 1, h - 1)) ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}"
                  proof
                    fix x
                    assume "x \<in> {(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h}"
                    then obtain h j where "x = (h, j)" "j \<le> i + 1" "h \<le> j" "0 < h" by blast
                    hence "j + 1 \<le> i + 2 \<and> h - 1 < j + 1 \<and> h - 1 \<le> i \<and> j + 1 \<noteq> h - 1 + 1 \<and> x = ((h - 1) + 1, (j + 1) - 1)"
                      by auto
                    thus "x \<in> (\<lambda>(h, j). (j + 1, h - 1)) ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}"
                      by (auto simp: image_iff)
                  qed
                qed
                show "inj_on (\<lambda>(h, j). (j + 1, h - 1)) {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}"
                proof
                  fix x y::"nat\<times>nat"
                  assume "x \<in> {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}" "y \<in> {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}"
                  thus "(case x of (h, j) \<Rightarrow> (j + 1, h - 1)) = (case y of (h, j) \<Rightarrow> (j + 1, h - 1)) \<Longrightarrow> x = y"
                    by auto
                qed
                show "\<And>x. x \<in> {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1} \<Longrightarrow>
                   (case case x of (h, j) \<Rightarrow> (j + 1, h - 1) of
                    (h, j) \<Rightarrow> coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) =
                   (case x of (h, j) \<Rightarrow> coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j))"
                  by fastforce
              qed
              have 2: "(\<Sum>h = 1..i + 1. coeff f h * coeff g (i + 2 - h) * coeff f (h - 1) * coeff g (i + 1 - h)) =
                    (\<Sum>(h, j)\<in>{(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}.
                     coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j))"
              proof (rule sum.reindex_cong)
                show "{1..i + 1} = fst ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}"
                proof
                  show "{1..i + 1} \<subseteq> fst ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}"
                  proof
                    fix x
                    assume "x \<in> {1..i + 1}"
                    hence "x \<le> i + 2 \<and> x - 1 < x \<and> x - 1 \<le> i \<and> x = x - 1 + 1 \<and> x = fst (x, x-1)"
                      by auto
                    thus "x \<in> fst ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}"
                      by blast
                  qed
                  show "fst ` {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1} \<subseteq> {1..i + 1}"
                    by force
                qed
                show "inj_on fst {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}"
                proof
                  fix x y
                  assume "x \<in> {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}"
                         "y \<in> {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}"
                  hence "x = (fst x, fst x - 1)" "y = (fst y, fst y - 1)" "fst x > 0" "fst y > 0"
                    by auto
                  thus "fst x = fst y \<Longrightarrow> x = y" by presburger
                qed
                show "\<And>x. x \<in> {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1} \<Longrightarrow>
                   coeff f (fst x) * coeff g (i + 2 - fst x) * coeff f (fst x - 1) * coeff g (i + 1 - fst x) =
                   (case x of (h, j) \<Rightarrow> coeff f h * coeff g (i + 2 - h) * coeff f j * coeff g (i - j))"
                  by fastforce
              qed
              have H: "{(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1} \<subseteq> {0..i+2}\<times>{0..i}"
                      "{(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1} \<subseteq> {0..i+2}\<times>{0..i}"
                      "finite ({0..i+2}\<times>{0..i})"
                by (fastforce, fastforce, fastforce)
              have "finite {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h \<noteq> j + 1}"
                   "finite {(h, j). h \<le> i + 2 \<and> j < h \<and> j \<le> i \<and> h = j + 1}"
                apply (rule finite_subset) using H apply (simp, simp)
                apply (rule finite_subset) using H apply (simp, simp)
                done
              thus ?thesis 
                apply (subst 1, subst 2, subst sum.union_disjoint[symmetric])
                   apply auto[3]
                apply (rule sum.cong)
                by auto
            qed
            ultimately show ?thesis
              by algebra
          qed

          text \<open>$\dots = \sum_{h \leq j} f_hf_j\left(g_{i+1-h}g_{i+1-j} - g_{i+2-h}g_{i-j}\right) + 
                         \sum_{h \leq j} f_{j+1}f_{h-1}\left(g_{i-j}g_{i+2-h} - g_{i+1-j}f_jg_{i+1-h}\right)$

                Note we have to also consider the edge cases caused by making these sums finite.\<close>
          also have "... =
              (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}.
                 coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) +
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                 coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j) - coeff g (i + 2 - h) * coeff g (i - j))) +
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                 coeff f (j+1) * coeff f (h-1) * (coeff g (i - j) * coeff g (i + 2 - h) - coeff g (i + 1 - j) * coeff g (i + 1 - h))) -
              ((\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                  coeff f (j+1) * coeff g (i + 1 - j) * coeff f (h-1) * coeff g (i + 1 - h)))" (is "?L = ?R")
          proof -
            have "?R = 
              (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}.
                 coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) +
              ((\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                 coeff f h * coeff f j * coeff g (i + 1 - h) * coeff g (i + 1 - j)) -
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                 coeff f h * coeff f j * coeff g (i + 2 - h) * coeff g (i - j))) +
              ((\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                 coeff f (j+1) * coeff f (h-1) * coeff g (i - j) * coeff g (i + 2 - h)) - 
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                 coeff f (j+1) * coeff f (h-1) * coeff g (i + 1 - j) * coeff g (i + 1 - h))) -
              ((\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                  coeff f (j+1) * coeff g (i + 1 - j) * coeff f (h-1) * coeff g (i + 1 - h)))"
              apply (subst sum_subtractf[symmetric], subst sum_subtractf[symmetric])
              by (auto simp: algebra_simps split_beta)
            also have "... =
                ((\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}.
                   coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) +
                (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                   coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j)))) -
                 (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                    coeff f h * coeff f j * coeff g (i + 2 - h) * coeff g (i - j)) +
                (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                    coeff f (j + 1) * coeff f (h - 1) * coeff g (i - j) * coeff g (i + 2 - h)) -
                ((\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                   coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) +
                (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                   coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)))"
              by (auto simp: algebra_simps)
            also have "... = ?L"
            proof -
              have "(\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}.
                       coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) +
                    (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
                       coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) =
                    (\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j}.
                       coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j)))"
              proof (subst sum.union_disjoint[symmetric])
                have "{(h, j). j = i + 1 \<and> h \<le> j} \<subseteq> {..i + 1} \<times> {..i + 1}"
                     "{(h, j). j \<le> i \<and> h \<le> j} \<subseteq> {..i + 1} \<times> {..i + 1}"
                  by (fastforce, fastforce)
                thus "finite {(h, j). j = i + 1 \<and> h \<le> j}" "finite {(h, j). j \<le> i \<and> h \<le> j}"
                  by (auto simp: finite_subset)
                show "{(h, j). j = i + 1 \<and> h \<le> j} \<inter> {(h, j). j \<le> i \<and> h \<le> j} = {}"
                  by fastforce
              qed (rule sum.cong, auto)
              moreover have "(\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                    coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) +
                 (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                    coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) =
                 (\<Sum>(h, j)\<in>{(h, j). j \<le> i + 1 \<and> h \<le> j \<and> 0 < h}.
                    coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h))"
              proof (subst sum.union_disjoint[symmetric])
                have "{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h} \<subseteq> {..i + 1} \<times> {..i + 1}"
                     "{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h} \<subseteq> {..i + 1} \<times> {..i + 1}"
                  by (fastforce, fastforce)
                thus "finite {(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}" "finite {(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}"
                  by (auto simp: finite_subset)
                show "{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h} \<inter> {(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h} = {}"
                  by fastforce
              qed (rule sum.cong, auto)
              ultimately show ?thesis 
                by (auto simp: algebra_simps)
            qed
            finally show ?thesis by presburger
          qed

          text \<open>$\dots = \sum_{h \leq j} \left(f_hf_j - f_{j+1}f_{h-1}\right)
                                         \left(g_{i+1-h}g_{i+1-j} - g_{i+2-h}g_{i-j}\right)$\<close>
          also have "... = 
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                 -(coeff f h * coeff f j - coeff f (j+1) * coeff f (h-1)) * (coeff g (i - j) * coeff g (i + 2 - h) - coeff g (i + 1 - j) * coeff g (i + 1 - h))) +
              (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> h = 0}.
                 coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j) - coeff g (i + 2 - h) * coeff g (i - j))) +
              (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}.
                 coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) -
              ((\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                  coeff f (j+1) * coeff g (i + 1 - j) * coeff f (h-1) * coeff g (i + 1 - h)))" (is "?L = ?R")
          proof -
            have "(\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j}.
               coeff f h * coeff f j *
               (coeff g (i + 1 - h) * coeff g (i + 1 - j) - coeff g (i + 2 - h) * coeff g (i - j))) =
             (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
               coeff f h * coeff f j *
               (coeff g (i + 1 - h) * coeff g (i + 1 - j) - coeff g (i + 2 - h) * coeff g (i - j))) +
             (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 = h}.
               coeff f h * coeff f j *
               (coeff g (i + 1 - h) * coeff g (i + 1 - j) - coeff g (i + 2 - h) * coeff g (i - j)))"
            proof (subst sum.union_disjoint[symmetric])
              have "{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h} \<subseteq> {..i}\<times>{..i}" "{(h, j). j \<le> i \<and> h \<le> j \<and> 0 = h} \<subseteq> {..i}\<times>{..i}"
                by (force, force)
              thus "finite {(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}" "finite {(h, j). j \<le> i \<and> h \<le> j \<and> 0 = h}"
                by (auto simp: finite_subset)
              show "{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h} \<inter> {(h, j). j \<le> i \<and> h \<le> j \<and> 0 = h} = {}"
                by fast
            qed (rule sum.cong, auto)
            
            moreover have "(\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
               (-coeff f h * coeff f j + coeff f (j + 1) * coeff f (h - 1)) *
               (coeff g (i - j) * coeff g (i + 2 - h) - coeff g (i + 1 - j) * coeff g (i + 1 - h))) =
                (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                   coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j) - coeff g (i + 2 - h) * coeff g (i - j))) +
                (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                   coeff f (j + 1) * coeff f (h - 1) *
                   (coeff g (i - j) * coeff g (i + 2 - h) - coeff g (i + 1 - j) * coeff g (i + 1 - h)))"
              by (subst sum.distrib[symmetric], rule sum.cong, fast, auto simp: algebra_simps)

            ultimately show ?thesis
              by (auto simp: algebra_simps)
          qed

          text \<open>$\dots \geq 0$ by \<open>normal_poly_general_coeff_mult\<close>\<close>
          also have "... \<ge> 0"
          proof -
            have "0 \<le> (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}.
                        - (coeff f h * coeff f j - coeff f (j + 1) * coeff f (h - 1)) *
                        (coeff g (i - j) * coeff g (i + 2 - h) - coeff g (i + 1 - j) * coeff g (i + 1 - h)))"
            proof (rule sum_nonneg)
              fix x assume "x \<in> {(h, j). j \<le> i \<and> h \<le> j \<and> 0 < h}"
              then obtain h j where H: "x = (h, j)" "j \<le> i" "h \<le> j" "0 < h" by fast
              hence "h - 1 \<le> j - 1" by force
              hence 1: "coeff f h * coeff f j - coeff f (j + 1) * coeff f (h - 1) \<ge> 0"
                using normal_poly_general_coeff_mult[OF hf, of "h-1" "j-1"] H
                by (auto simp: algebra_simps)
              from H have "i - j \<le> i - h" by force
              hence 2: "coeff g (i - j) * coeff g (i + 2 - h) - coeff g (i + 1 - j) * coeff g (i + 1 - h) \<le> 0"
                using normal_poly_general_coeff_mult[OF hg, of "i - j" "i - h"] H
                by (smt (verit, del_insts) Nat.add_diff_assoc2 le_trans)
              show "0 \<le> (case x of
               (h, j) \<Rightarrow>
                 - (coeff f h * coeff f j - coeff f (j + 1) * coeff f (h - 1)) *
                 (coeff g (i - j) * coeff g (i + 2 - h) -
                  coeff g (i + 1 - j) * coeff g (i + 1 - h)))"
                apply (subst H(1), subst split, rule mult_nonpos_nonpos, subst neg_le_0_iff_le)
                subgoal using 1 by blast
                subgoal using 2 by blast
                done
            qed
            moreover have "0 \<le> (\<Sum>(h, j)\<in>{(h, j). j \<le> i \<and> h \<le> j \<and> h = 0}.
                        coeff f h * coeff f j *
                        (coeff g (i + 1 - h) * coeff g (i + 1 - j) - coeff g (i + 2 - h) * coeff g (i - j)))"
            proof (rule sum_nonneg)
              fix x assume "x \<in> {(h, j). j \<le> i \<and> h \<le> j \<and> h = 0}"
              then obtain h j where H: "x = (h, j)" "j \<le> i" "h \<le> j" "h = 0" by fast
              have 1: "coeff f h * coeff f j \<ge> 0"
                by (simp add: hf normal_coeff_nonneg)
              from H have "i - j \<le> i - h" by force
              hence 2: "coeff g (i - j) * coeff g (i + 2 - h) - coeff g (i + 1 - j) * coeff g (i + 1 - h) \<le> 0"
                using normal_poly_general_coeff_mult[OF hg, of "i - j" "i - h"] H
                by (smt (verit, del_insts) Nat.add_diff_assoc2 le_trans)
              show "0 \<le> (case x of
               (h, j) \<Rightarrow>
                 coeff f h * coeff f j *
                 (coeff g (i + 1 - h) * coeff g (i + 1 - j) -
                  coeff g (i + 2 - h) * coeff g (i - j)))"
                apply (subst H(1), subst split, rule mult_nonneg_nonneg)
                subgoal using 1 by blast
                subgoal using 2 by argo
                done
            qed
            moreover have "0 \<le> (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}. coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) -
                 (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                    coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h))"
            proof -
              have "(\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}. coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) -
                 (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                    coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) = 
                 (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> h = 0}. coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) +
                 (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}. coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) -
                 (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                    coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h))"
              proof (subst sum.union_disjoint[symmetric])
                have "{(h, j). j = i + 1 \<and> h \<le> j \<and> h = 0} = {(0, i + 1)}"
                     "{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h} = {1..i+1} \<times> {i + 1}"
                  by (fastforce, force)
                thus "finite {(h, j). j = i + 1 \<and> h \<le> j \<and> h = 0}"
                     "finite {(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}"
                  by auto
                show "{(h, j). j = i + 1 \<and> h \<le> j \<and> h = 0} \<inter> {(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h} = {}" 
                  by fastforce
                have "{(h, j). j = i + 1 \<and> h \<le> j \<and> h = 0} \<union> {(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h} = {(h, j). j = i + 1 \<and> h \<le> j}"
                  by fastforce
                thus "(\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j}. coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) -
                      (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                         coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h)) =
                      (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> h = 0} \<union> {(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                         coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) -
                      (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                         coeff f (j + 1) * coeff g (i + 1 - j) * coeff f (h - 1) * coeff g (i + 1 - h))"
                  by presburger
              qed
              also have "... =
                (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> h = 0}. coeff f h * coeff f j * (coeff g (i + 1 - h) * coeff g (i + 1 - j))) +
                (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}. 
                   (coeff f h * coeff f j - coeff f (j + 1) * coeff f (h - 1)) * (coeff g (i + 1 - h) * coeff g (i + 1 - j)))"
                by (subst add_diff_eq[symmetric], subst sum_subtractf[symmetric], subst add_left_cancel, rule sum.cong, auto simp: algebra_simps)
              also have "... \<ge> 0"
              proof (rule add_nonneg_nonneg)
                show "0 \<le> (\<Sum>(h, j)\<in>{(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}.
                        (coeff f h * coeff f j - coeff f (j + 1) * coeff f (h - 1)) *
                        (coeff g (i + 1 - h) * coeff g (i + 1 - j)))"
                proof (rule sum_nonneg)
                  fix x assume "x \<in> {(h, j). j = i + 1 \<and> h \<le> j \<and> 0 < h}"
                  then obtain h j where H: "x = (h, j)" "j = i + 1" "h \<le> j" "0 < h" by fast
                  hence "h - 1 \<le> j - 1" by force
                  hence 1: "coeff f h * coeff f j - coeff f (j + 1) * coeff f (h - 1) \<ge> 0"
                    using normal_poly_general_coeff_mult[OF hf, of "h-1" "j-1"] H
                    by (auto simp: algebra_simps)
                  hence 2: "0 \<le> coeff g (i + 1 - h) * coeff g (i + 1 - j)"
                    by (meson hg mult_nonneg_nonneg normal_coeff_nonneg)
                  show "0 \<le> (case x of
                   (h, j) \<Rightarrow>
                     (coeff f h * coeff f j - coeff f (j + 1) * coeff f (h - 1)) *
                     (coeff g (i + 1 - h) * coeff g (i + 1 - j)))"
                    apply (subst H(1), subst split, rule mult_nonneg_nonneg)
                    subgoal using 1 by blast
                    subgoal using 2 by blast
                    done
                qed
              qed (rule sum_nonneg, auto simp: hf hg normal_coeff_nonneg)[1]
              finally show ?thesis .
            qed
            ultimately show ?thesis by auto
          qed
          finally show "coeff (f * g) i * coeff (f * g) (i + 2) \<le> (coeff (f * g) (i + 1))\<^sup>2" by (auto simp: power2_eq_square)
        qed
        moreover have "\<And>i j k. i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> 0 < coeff (f*g) i \<Longrightarrow> 0 < coeff (f*g) k \<Longrightarrow> 0 < coeff (f*g) j"
        proof -
          fix j k
          assume "0 < coeff (f * g) k"
          hence "k \<le> degree (f * g)" using le_degree by force
          moreover assume "j \<le> k"
          ultimately have "j \<le> degree (f * g)" by auto
          hence 1: "j \<le> degree f + degree g"
            by (simp add: degree_mult_eq hf hg normal_non_zero)
          show "0 < coeff (f * g) j"
            apply (subst coeff_mult, rule sum_pos2[of _ "min j (degree f)"], simp, simp)
            apply (rule mult_pos_pos, rule normal_of_no_zero_root, simp add: hf0, simp)
            using hf apply auto[1]
             apply (rule normal_of_no_zero_root)
               apply (simp add: hg0)
            using 1 apply force
            using hg apply auto[1]
            by (simp add: hf hg normal_coeff_nonneg)
        qed
        ultimately show "normal_poly (f*g)" 
          by (rule normal_polyI)
      qed
    qed
  qed
qed

lemma normal_poly_of_roots: 
  fixes p::"real poly"
  assumes "\<And>z. poly (map_poly complex_of_real p) z = 0 
        \<Longrightarrow> Re z \<le> 0 \<and> 4*(Re z)^2 \<ge> (cmod z)^2"
      and "lead_coeff p = 1"
  shows "normal_poly p"
  using assms
proof (induction p rule: real_poly_roots_induct)
  fix p::"real poly" and x::real
  assume "lead_coeff (p * [:- x, 1:]) = 1"
  hence 1: "lead_coeff p = 1"
    by (metis coeff_degree_mult lead_coeff_pCons(1) mult_cancel_left1 pCons_one zero_neq_one)
  assume h: "(\<And>z. poly (map_poly complex_of_real (p * [:- x, 1:])) z = 0 \<Longrightarrow>
                 Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2)"
  hence 2: "(\<And>z. poly (map_poly complex_of_real p) z = 0 \<Longrightarrow>
                 Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2)"
    by (metis (no_types, hide_lams) four_x_squared mult.commute mult_cancel_left1 of_real_poly_map_mult poly_mult)
  have 3: "normal_poly [:-x, 1:]"
    apply (subst linear_normal_iff, 
        subst Re_complex_of_real[symmetric], rule conjunct1)
    by (rule h[of x], subst of_real_poly_map_poly[symmetric], force)
  assume "(\<And>z. poly (map_poly complex_of_real p) z = 0
             \<Longrightarrow> Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2) \<Longrightarrow>
            lead_coeff p = 1 \<Longrightarrow> normal_poly p"
  hence "normal_poly p" using 1 2 by fast
  then show "normal_poly (p * [:-x, 1:])" 
    using 3 by (rule normal_mult)
next
  fix p::"real poly" and a b::real
  assume "lead_coeff (p * [:a * a + b * b, - 2 * a, 1:]) = 1"
  hence 1: "lead_coeff p = 1"
    by (smt (verit) coeff_degree_mult lead_coeff_pCons(1) mult_cancel_left1 pCons_eq_0_iff pCons_one)
  assume h: "(\<And>z. poly (map_poly complex_of_real (p * [:a * a + b * b, - 2 * a, 1:])) z = 0 \<Longrightarrow>
                 Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2)"
  hence 2: "(\<And>z. poly (map_poly complex_of_real p) z = 0 \<Longrightarrow>
                 Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2)"
  proof -
    fix z :: complex
    assume "poly (map_poly complex_of_real p) z = 0"
    then have "\<forall>q. 0 = poly (map_poly complex_of_real (p * q)) z"
      by simp
    then show "Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2"
      using h by presburger
  qed
  have 3: "[:a * a + b * b, - 2 * a, 1:] = [:cmod (a + \<i>*b) ^ 2, -2 * Re (a + \<i>*b), 1:]"
    by (force simp: cmod_def power2_eq_square)
  interpret map_poly_idom_hom complex_of_real ..
  have 4: "normal_poly [:a * a + b * b, - 2 * a, 1:]"
    apply (subst 3, subst quadratic_normal_iff)
    apply (rule h, unfold hom_mult poly_mult)
    by (auto simp: algebra_simps)
  assume "(\<And>z. poly (map_poly complex_of_real p) z = 0 \<Longrightarrow> Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2) \<Longrightarrow>
            lead_coeff p = 1 \<Longrightarrow> normal_poly p"
  hence "normal_poly p" using 1 2 by fast
  then show "normal_poly (p * [:a * a + b * b, - 2 * a, 1:])" 
    using 4 by (rule normal_mult)
next
  fix a::real 
  assume "lead_coeff [:a:] = 1"
  moreover have "\<And>i j k.
       lead_coeff [:a:] = 1 \<Longrightarrow>
       i \<le> j \<Longrightarrow>
       j \<le> k \<Longrightarrow> 0 < coeff [:a:] i \<Longrightarrow> 0 < coeff [:a:] k \<Longrightarrow> 0 < coeff [:a:] j"
    by (metis bot_nat_0.extremum_uniqueI coeff_eq_0 degree_pCons_0 leI 
        less_numeral_extra(3))
  ultimately show "normal_poly [:a:]"
    apply (subst normal_polyI)
    by (auto simp:pCons_one)
qed

lemma normal_changes: 
  fixes f::"real poly"
  assumes hf: "normal_poly f" and hx: "x > 0"
  defines "df \<equiv> degree f"
  shows "changes (coeffs (f*[:-x,1:])) = 1"
  using df_def hf 
proof (induction df arbitrary: f)
  case 0
  then obtain a where "f = [:a:]" using degree_0_iff by auto
  thus "changes (coeffs (f*[:-x, 1:])) = 1"
    using normal_non_zero[OF \<open>normal_poly f\<close>] hx 
    by (auto simp: algebra_simps zero_less_mult_iff mult_less_0_iff)
next
  case (Suc df)
  then show ?case
  proof (cases "poly f 0 = 0")
    assume "poly f 0 = 0" and hf:"normal_poly f"
    moreover then obtain f' where hdiv: "f = f'*[:0, 1:]"
      by (smt (verit) dvdE mult.commute poly_eq_0_iff_dvd) 
    ultimately have hf': "normal_poly f'" using normal_divide_x by blast
    assume "Suc df = degree f"
    hence "degree f' = df" using hdiv normal_non_zero[OF hf'] by (auto simp: degree_mult_eq)
    moreover assume "\<And>f::real poly. df = degree f \<Longrightarrow> normal_poly f \<Longrightarrow> changes (coeffs (f * [:- x, 1:])) = 1"
    ultimately have "changes (coeffs (f' * [:- x, 1:])) = 1" using hf' by fast
    thus "changes (coeffs (f * [:- x, 1:])) = 1"
      apply (subst hdiv, subst mult_pCons_right, subst smult_0_left, subst add_0)
      apply (subst mult_pCons_left, subst smult_0_left, subst add_0)
      by (subst changes_pCons, auto)
  next
    assume hf:"normal_poly f" and "poly f 0 \<noteq> 0"
    hence h': "\<And>i. i \<le> degree f \<Longrightarrow> coeff f i > 0"
      by (auto simp: normal_of_no_zero_root)
    hence "\<And>i. i < degree f - 1 \<Longrightarrow> (coeff f i)/(coeff f (i+1)) \<le> (coeff f (i+1))/(coeff f (i+2))"
      using normal_poly_coeff_mult[OF hf] normal_coeff_nonneg[OF hf]
      by (auto simp: divide_simps power2_eq_square)
    hence h'': "\<And>i. i < degree f - 1 \<Longrightarrow> (coeff f i)/(coeff f (i+1)) - x \<le> (coeff f (i+1))/(coeff f (i+2)) - x"
      by fastforce
    have hdeg: "degree (pCons 0 f - smult x f) = degree f + 1"
      apply (subst diff_conv_add_uminus)
      apply (subst degree_add_eq_left)
      by (auto simp: hf normal_non_zero)

    let ?f = "\<lambda> z w. \<lambda>i. if i=0 then z/(x * coeff f 0) else (if i = degree (pCons 0 f - smult x f) then w/(lead_coeff f) else inverse (coeff f i))"

    have 1: "\<And>z w. 0 < z \<Longrightarrow> 0 < w \<Longrightarrow> changes (coeffs (f * [:-x, 1:])) =
          changes (-z # map (\<lambda>i. (coeff f (i-1))/(coeff f i) - x) [1..<degree (pCons 0 f - smult x f)] @ [w])"
    proof -
      fix z w :: real
      assume hz: "0 < z" and hw: "0 < w"

      have "-z # map (\<lambda>i. (coeff f (i-1))/(coeff f i) - x) [1..<degree (pCons 0 f - smult x f)] @ [w] =
            map (\<lambda>i. if i = 0 then -z else if i = degree (pCons 0 f - smult x f) then w else 
              (coeff f (i-1))/(coeff f i) - x) [0..<degree (pCons 0 f - smult x f) + 1]"
      proof (rule nth_equalityI)
        fix i assume "i < length (- z # map (\<lambda>i. coeff f (i - 1) / coeff f i - x) [1..<degree (pCons 0 f - smult x f)] @ [w])"
        hence "i \<le> degree (pCons 0 f - smult x f)"
          using hdeg Suc.hyps(2) by auto
        then consider (a)"i = 0" | (b)"(0 < i \<and> i < degree (pCons 0 f - smult x f))" |
          (c)"i = degree (pCons 0 f - smult x f)"
          by fastforce
        then show "(- z #
              map (\<lambda>i. coeff f (i - 1) / coeff f i - x)
               [1..<degree (pCons 0 f - smult x f)] @
              [w]) ! i =
             map (\<lambda>i. if i = 0 then - z
                      else if i = degree (pCons 0 f - smult x f) then w
                           else coeff f (i - 1) / coeff f i - x)
              [0..<degree (pCons 0 f - smult x f) + 1] ! i"
          apply (cases)
          by (auto simp: nth_append)
      qed (force simp: hdeg)      

      also have "... = [?f z w i * (nth_default 0 (coeffs (f * [:-x, 1:])) i). 
                        i \<leftarrow> [0..<Suc (degree (pCons 0 f - smult x f))]]"
      proof (rule map_cong)
        fix i assume "i \<in> set [0..<Suc (degree (pCons 0 f - smult x f))]"
        then consider (a)"i = 0" | (b)"(0 \<noteq> i \<and> i < degree (pCons 0 f - smult x f))" |
          (c)"i = degree (pCons 0 f - smult x f)"
          by fastforce
        then show "(if i = 0 then - z
           else if i = degree (pCons 0 f - smult x f) then w
                else coeff f (i - 1) / coeff f i - x) =
          (if i = 0 then z / (x * coeff f 0)
           else if i = degree (pCons 0 f - smult x f) then w / lead_coeff f
                else inverse (coeff f i)) *
          nth_default 0 (coeffs (f * [:- x, 1:])) i"
        proof (cases)
          case (a)
          thus ?thesis using hx \<open>poly f 0 \<noteq> 0\<close> by (auto simp: nth_default_coeffs_eq poly_0_coeff_0)
        next
          case (b)
          thus ?thesis using hx h'[of i] hdeg
            by (auto simp: field_simps nth_default_coeffs_eq coeff_pCons nat.split poly_0_coeff_0)
        next
          case (c)
          thus ?thesis using hdeg by (auto simp: nth_default_coeffs_eq coeff_eq_0)
        qed
      qed force

      finally have 1: " - z #
        map (\<lambda>i. coeff f (i - 1) / coeff f i - x) [1..<degree (pCons 0 f - smult x f)] @ [w] =
        map (\<lambda>i. (if i = 0 then z / (x * coeff f 0)
                  else if i = degree (pCons 0 f - smult x f) then w / lead_coeff f
                       else inverse (coeff f i)) *
                 nth_default 0 (coeffs (f * [:- x, 1:])) i)
         [0..<Suc (degree (pCons 0 f - smult x f))]" .

      have "f * [:-x, 1:] \<noteq> 0" using hdeg by force

      show "changes (coeffs (f * [:- x, 1:])) =
           changes
            (- z #
             map (\<lambda>i. coeff f (i - 1) / coeff f i - x)
              [1..<degree (pCons 0 f - smult x f)] @
             [w])"
        apply (subst 1)
        apply (rule changes_scale[symmetric])
        subgoal using hz hw hx h' hdeg by auto
        subgoal using hdeg \<open>f * [:-x, 1:] \<noteq> 0\<close> 
          by (auto simp: length_coeffs)
        done
    qed

    hence "changes (coeffs (f * [:- x, 1:])) =
        changes
         (- (max 1 (-(coeff f 0 / coeff f 1 - x))) #
          map (\<lambda>i. coeff f (i - 1) / coeff f i - x)
           [1..<degree (pCons 0 f - smult x f)] @
          [max 1 (coeff f (degree f - 1) / lead_coeff f - x)])"
      by force

    also have "... = 1"
    proof (rule changes_increasing)
      fix i
      assume "i < length
              (- max 1 (- (coeff f 0 / coeff f 1 - x)) #
               map (\<lambda>i. coeff f (i - 1) / coeff f i - x) [1..<degree (pCons 0 f - smult x f)] @
               [max 1 (coeff f (degree f - 1) / lead_coeff f - x)]) - 1"
      hence "i < degree (pCons 0 f - smult x f)"
        using hdeg Suc.hyps(2) by fastforce
      then consider (a)"i = 0" | (b)"0 \<noteq> i \<and> i < degree (pCons 0 f - smult x f) - 1" |
        (c)"i = degree (pCons 0 f - smult x f) - 1"
        by fastforce
      then show "(- max 1 (- (coeff f 0 / coeff f 1 - x)) #
          map (\<lambda>i. coeff f (i - 1) / coeff f i - x)
           [1..<degree (pCons 0 f - smult x f)] @
          [max 1 (coeff f (degree f - 1) / lead_coeff f - x)]) !
         i
         \<le> (- max 1 (- (coeff f 0 / coeff f 1 - x)) #
             map (\<lambda>i. coeff f (i - 1) / coeff f i - x)
              [1..<degree (pCons 0 f - smult x f)] @
             [max 1 (coeff f (degree f - 1) / lead_coeff f - x)]) !
            (i + 1)"
      proof (cases)
        case a
        then show ?thesis by (auto simp: nth_append)
      next
        case b
        have "coeff f (i - 1) * coeff f (i - 1 + 2) \<le> (coeff f (i - 1 + 1))\<^sup>2"
          by (rule normal_poly_coeff_mult[OF hf, of "i - 1"])
        hence "coeff f (i - 1) / coeff f i \<le> coeff f i / coeff f (i + 1)"
          using h'[of i] h'[of "i+1"] h'[of "i-1"] h' b hdeg
          by (auto simp: power2_eq_square divide_simps)
        then show ?thesis
          using b by (auto simp: nth_append)
      next
        case c
        then show ?thesis using hdeg by (auto simp: nth_append not_le)
      qed
    qed auto

    finally show "changes (coeffs (f * [:-x, 1:])) = 1" .
  qed
qed

end