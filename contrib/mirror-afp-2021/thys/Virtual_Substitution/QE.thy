section "QE lemmas"
theory QE
  imports Polynomials.MPoly_Type_Univariate
    Polynomials.Polynomials  Polynomials.MPoly_Type_Class_FMap 
    "HOL-Library.Quadratic_Discriminant"
begin

(* This file may take some time to load *)

subsection "Useful Definitions/Setting Up"

definition sign:: "real Polynomial.poly \<Rightarrow> real \<Rightarrow> int"
  where "sign p x \<equiv> (if poly p x = 0 then 0 else (if poly p x > 0 then 1 else -1))"

definition sign_num:: "real \<Rightarrow> int"
  where "sign_num x \<equiv> (if x = 0 then 0 else (if x > 0 then 1 else -1))"

definition root_list:: "real Polynomial.poly \<Rightarrow> real set"
  where "root_list p \<equiv> ({(x::real). poly p x = 0}::real set)" 

definition root_set:: "(real \<times> real \<times> real) set \<Rightarrow> real set"
  where "root_set les \<equiv> ({(x::real). (\<exists> (a, b, c) \<in> les. a*x^2 + b*x + c = 0)}::real set)" 

definition sorted_root_list_set:: "(real \<times> real \<times> real) set \<Rightarrow> real list"
  where "sorted_root_list_set p \<equiv> sorted_list_of_set (root_set p)" 

definition nonzero_root_set:: "(real \<times> real \<times> real) set \<Rightarrow> real set"
  where "nonzero_root_set les \<equiv> ({(x::real). (\<exists> (a, b, c) \<in> les. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a*x^2 + b*x + c = 0)}::real set)" 

definition sorted_nonzero_root_list_set:: "(real \<times> real \<times> real) set \<Rightarrow> real list"
  where "sorted_nonzero_root_list_set p \<equiv> sorted_list_of_set (nonzero_root_set p)" 


(* Important property of sorted lists *)
lemma sorted_list_prop:
  fixes l::"real list"
  fixes x::"real"
  assumes sorted: "sorted l"
  assumes lengt: "length l > 0"
  assumes xgt: "x > l ! 0"
  assumes xlt: "x \<le> l ! (length l - 1)"
  shows "\<exists>n. (n+1) < (length l) \<and> x \<ge> l !n \<and> x \<le> l ! (n + 1)"
proof - 
  have "\<not>(\<exists>n. (n+1) < (length l) \<and> x \<ge> l !n \<and> x \<le> l ! (n + 1)) \<Longrightarrow> False"
  proof clarsimp 
    fix n
    assume alln: "\<forall>n. l ! n \<le> x \<longrightarrow> Suc n < length l \<longrightarrow> \<not> x \<le> l ! Suc n"
    have "\<forall>k. (k < length l \<longrightarrow> x > l ! k)" 
    proof clarsimp 
      fix k
      show "k < length l \<Longrightarrow> l ! k < x"
      proof (induct k)
        case 0
        then show ?case using xgt by auto
      next
        case (Suc k)
        then show ?case using alln
          using less_eq_real_def by auto 
      qed
    qed
    then show "False"
      using xlt diff_Suc_less lengt not_less
      by (metis One_nat_def) 
  qed
  then show ?thesis by auto
qed


subsection "Quadratic polynomial properties"
lemma quadratic_poly_eval: 
  fixes a b c::"real"
  fixes x::"real"
  shows "poly [:c, b, a:] x = a*x^2 + b*x + c"    
proof - 
  have "x * (b + x * a) = a * x\<^sup>2 + b * x" by (metis add.commute distrib_right mult.assoc mult.commute power2_eq_square)
  then show ?thesis by auto
qed

lemma poly_roots_set_same:
  fixes a b c:: "real"
  shows "{(x::real). a * x\<^sup>2 + b * x + c = 0} = {x. poly [:c, b, a:] x = 0}"
proof - 
  have "\<forall>x. a*x^2 + b*x + c = poly [:c, b, a:] x"
  proof clarsimp 
    fix x
    show "a * x\<^sup>2 + b * x = x * (b + x * a)"
      using quadratic_poly_eval[of c b a x] by auto
  qed
  then show ?thesis 
    by auto
qed

lemma root_set_finite:
  assumes fin: "finite les"
  assumes nex: "\<not>(\<exists> (a, b, c) \<in> les. a = 0 \<and> b = 0 \<and> c = 0 )"
  shows "finite (root_set les)"
proof - 
  have "\<forall>(a, b, c) \<in> les. finite {(x::real). a*x^2 + b*x + c = 0}" 
  proof clarsimp 
    fix a b c
    assume "(a, b, c) \<in> les"
    then have "[:c, b, a:] \<noteq> 0" using nex by auto
    then have "finite {x. poly [:c, b, a:] x = 0}"
      using poly_roots_finite[where p = "[:c, b, a:]"] by auto
    then show "finite {x. a * x\<^sup>2 + b * x + c = 0}"
      using  poly_roots_set_same by auto
  qed
  then show ?thesis using fin
    unfolding root_set_def by auto
qed

lemma nonzero_root_set_finite:
  assumes fin: "finite les"
  shows "finite (nonzero_root_set les)"
proof - 
  have "\<forall>(a, b, c) \<in> les. (a \<noteq> 0 \<or> b \<noteq> 0) \<longrightarrow> finite {(x::real). a*x^2 + b*x + c = 0}" 
  proof clarsimp 
    fix a b c
    assume ins: "(a, b, c) \<in> les"
    assume "a = 0 \<longrightarrow> b \<noteq> 0"
    then have "[:c, b, a:] \<noteq> 0" using ins by auto
    then have "finite {x. poly [:c, b, a:] x = 0}"
      using poly_roots_finite[where p = "[:c, b, a:]"] by auto
    then show "finite {x. a * x\<^sup>2 + b * x + c = 0}"
      using  poly_roots_set_same by auto
  qed
  then show ?thesis using fin
    unfolding nonzero_root_set_def by auto
qed

lemma discriminant_lemma:
  fixes a b c r::"real"
  assumes aneq: "a \<noteq> 0"
  assumes beq: "b = 2 * a * r"
  assumes root: " a * r^2 - 2 * a * r*r + c = 0"
  shows "\<forall>x. a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> x = -r"
proof - 
  have "c = a*r^2" using root
    by (simp add: power2_eq_square)
  then have same: "b^2 - 4*a*c = (2 * a * r)^2 - 4*a*(a*r^2)" using beq
    by blast 
  have "(2 * a * r)^2 = 4*a^2*r^2"
    by (simp add: mult.commute power2_eq_square)
  then have "(2 * a * r)^2 - 4*a*(a*(r)^2) = 0"
    using power2_eq_square by auto 
  then have "b^2 - 4*a*c = 0" using same
    by simp 
  then have "\<forall>x. a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> x = -b / (2 * a)"
    using discriminant_zero aneq unfolding discrim_def by auto
  then show ?thesis using beq
    by (simp add: aneq) 
qed

(* Show a polynomial only changes sign when it passes through a root *)
lemma changes_sign:
  fixes p:: "real Polynomial.poly"
  shows "\<forall>x::real. \<forall> y::real. ((sign p x \<noteq> sign p y  \<and> x < y) \<longrightarrow> (\<exists>c \<in> (root_list p). x \<le> c \<and> c \<le> y))"
proof clarsimp
  fix x y
  assume "sign p x \<noteq> sign p y"
  assume "x < y"
  then show "\<exists>c\<in>root_list p. x \<le> c \<and> c \<le> y"
    using poly_IVT_pos[of x y p] poly_IVT_neg[of x y p] 
    by (metis (mono_tags) \<open>sign p x \<noteq> sign p y\<close> less_eq_real_def linorder_neqE_linordered_idom mem_Collect_eq root_list_def sign_def)
qed

(* Show a polynomial only changes sign if it passes through a root *)
lemma changes_sign_var:
  fixes a b c x y:: "real"
  shows "((sign_num (a*x^2 + b*x + c) \<noteq> sign_num (a*y^2 + b*y + c)  \<and> x < y) \<Longrightarrow> (\<exists>q. (a*q^2 + b*q + c = 0 \<and> x \<le> q \<and> q \<le> y)))"
proof  clarsimp
  assume sn: "sign_num (a * x\<^sup>2 + b * x + c) \<noteq> sign_num (a * y\<^sup>2 + b * y + c)"
  assume xy: " x < y"
  let ?p = "[:c, b, a:]"
  have cs: "((sign ?p x \<noteq> sign ?p y  \<and> x < y) \<longrightarrow> (\<exists>c \<in> (root_list ?p). x \<le> c \<and> c \<le> y))"
    using changes_sign[of ?p] by auto
  have "(sign ?p x \<noteq> sign ?p y  \<and> x < y)"
    using sn xy unfolding sign_def sign_num_def using quadratic_poly_eval
    by presburger 
  then have "(\<exists>c \<in> (root_list ?p). x \<le> c \<and> c \<le> y)" 
    using cs 
    by auto 
  then obtain q where "q \<in> root_list ?p \<and> x \<le> q \<and> q \<le> y" 
    by auto
  then have "a*q^2 + b*q + c = 0 \<and> x \<le> q \<and> q \<le> y"
    unfolding root_list_def using quadratic_poly_eval[of c b a q]
    by auto
  then show "\<exists>q. a * q\<^sup>2 + b * q + c = 0 \<and> x \<le> q \<and> q \<le> y"  
    by auto
qed

subsection "Continuity Properties"
lemma continuity_lem_eq0:
  fixes p::"real"
  shows "r < p \<Longrightarrow> \<forall>x\<in>{r <..p}. a * x\<^sup>2 + b * x + c = 0 \<Longrightarrow> (a = 0 \<and> b = 0 \<and> c = 0)" 
proof - 
  assume r_lt: "r < p"
  assume inf_zer: "\<forall>x\<in>{r <..p}. a * x\<^sup>2 + b * x + c = 0"
  have nf: "\<not>finite {r..<p}" using Set_Interval.dense_linorder_class.infinite_Ioo r_lt by auto
  have "\<not>(a = 0 \<and> b = 0 \<and> c = 0) \<Longrightarrow> False"
  proof - 
    assume "\<not>(a = 0 \<and> b = 0 \<and> c = 0)"
    then have "[:c, b, a:] \<noteq> 0" by auto
    then have fin: "finite {x. poly [:c, b, a:] x = 0}" using poly_roots_finite[where p = "[:c, b, a:]"] by auto
    have "{x. a*x^2 + b*x + c = 0} = {x. poly [:c, b, a:] x = 0}" using quadratic_poly_eval by auto
    then have finset: "finite {x. a*x^2 + b*x + c = 0}"  using fin by auto
    have "{r <..p} \<subseteq> {x. a*x^2 + b*x + c = 0}" using inf_zer by blast
    then show "False" using finset nf
      using finite_subset
      by (metis (no_types, lifting) infinite_Ioc_iff r_lt) 
  qed
  then show "(a = 0 \<and> b = 0 \<and> c = 0)" by auto
qed

lemma continuity_lem_lt0: 
  fixes r:: "real"
  fixes a b c:: "real"
  shows "poly [:c, b, a:] r < 0 \<Longrightarrow>
    \<exists>y'> r. \<forall>x\<in>{r<..y'}. poly [:c, b, a:] x < 0"
proof - 
  let ?f = "poly [:c,b,a:]"
  assume r_ltz: "poly [:c, b, a:] r < 0"
  then have "[:c, b, a:] \<noteq> 0" by auto
  then have "finite {x. poly [:c, b, a:] x = 0}" using poly_roots_finite[where p = "[:c, b, a:]"]    
    by auto
  then have fin: "finite  {x. x > r \<and> poly [:c, b, a:] x = 0}"
    using finite_Collect_conjI by blast 
  let ?l = "sorted_list_of_set {x. x > r \<and> poly [:c, b, a:] x = 0}"
  show ?thesis proof (cases "length ?l = 0")
    case True
    then have no_zer: "\<not>(\<exists>x>r. poly [:c, b, a:] x = 0)" using sorted_list_of_set_eq_Nil_iff fin by auto
    then have "\<And>y. y > r \<and> y < (r + 1) \<Longrightarrow> poly [:c, b, a:] y < 0 " 
    proof - 
      fix y
      assume "y > r \<and> y < r + 1"
      then show "poly [:c, b, a:] y < 0"
        using r_ltz no_zer poly_IVT_pos[where a = "r", where p = "[:c, b, a:]", where b = "y"]
        by (meson linorder_neqE_linordered_idom)
    qed
    then show ?thesis
      by (metis (no_types, hide_lams) \<open>\<not> (\<exists>x>r. poly [:c, b, a:] x = 0)\<close> \<open>poly [:c, b, a:] r < 0\<close> greaterThanAtMost_iff linorder_neqE_linordered_idom linordered_field_no_ub poly_IVT_pos) 
  next
    case False
    then have len_nonz: "length (sorted_list_of_set {x. r < x \<and> poly [:c, b, a:] x = 0}) \<noteq> 0"
      by blast 
    then have "\<forall>n \<in> {x. x > r \<and> poly [:c, b, a:] x = 0}. (nth_default 0 ?l 0) \<le> n"
      using fin set_sorted_list_of_set sorted_sorted_list_of_set
      using  in_set_conv_nth leI not_less0 sorted_nth_mono
      by (smt not_less_iff_gr_or_eq nth_default_def)
    then have no_zer: "\<not>(\<exists>x>r. (x < (nth_default 0 ?l 0) \<and> poly [:c, b, a:] x = 0))"
      using sorted_sorted_list_of_set by auto
    then have fa: "\<And>y. y > r \<and> y < (nth_default 0 ?l 0) \<Longrightarrow> poly [:c, b, a:] y < 0 " 
    proof - 
      fix y
      assume "y > r \<and> y < (nth_default 0 ?l 0)"
      then show "poly [:c, b, a:] y < 0"
        using r_ltz no_zer poly_IVT_pos[where a = "r", where p = "[:c, b, a:]", where b = "y"]
        by (meson less_imp_le less_le_trans linorder_neqE_linordered_idom)
    qed
    have "nth_default 0 ?l 0 > r" using fin set_sorted_list_of_set
      using len_nonz length_0_conv length_greater_0_conv mem_Collect_eq nth_mem
      by (metis (no_types, lifting) nth_default_def)
    then have "\<exists>(y'::real). r < y' \<and> y' < (nth_default 0 ?l 0)"
      using dense by blast
    then obtain y' where y_prop:"r < y' \<and>y' < (nth_default 0 ?l 0)" by auto
    then have "\<forall>x\<in>{r<..y'}. poly [:c, b, a:] x < 0"
      using fa by auto
    then show ?thesis using y_prop by blast 
  qed
qed

lemma continuity_lem_gt0: 
  fixes r:: "real"
  fixes a b c:: "real"
  shows "poly [:c, b, a:] r > 0 \<Longrightarrow>
    \<exists>y'> r. \<forall>x\<in>{r<..y'}. poly [:c, b, a:] x > 0"
proof -
  assume r_gtz: "poly [:c, b, a:] r > 0 "
  let ?p = "[:-c, -b, -a:]"
  have revpoly: "\<forall>x. -1*(poly [:c, b, a:] x) = poly [:-c, -b, -a:] x"
    by (metis (no_types, hide_lams) Polynomial.poly_minus add.inverse_neutral minus_pCons mult_minus1)
  then have "poly ?p r < 0" using r_gtz
    by (metis mult_minus1 neg_less_0_iff_less)
  then have "\<exists>y'> r. \<forall>x\<in>{r<..y'}. poly ?p x < 0" using continuity_lem_lt0
    by blast
  then obtain y' where y_prop: "y' > r \<and> (\<forall>x\<in>{r<..y'}. poly ?p x < 0)" by auto
  then have "\<forall>x\<in>{r<..y'}. poly [:c, b, a:] x > 0 " using revpoly
    using neg_less_0_iff_less by fastforce
  then show ?thesis 
    using y_prop  by blast 
qed

lemma continuity_lem_lt0_expanded: 
  fixes r:: "real"
  fixes a b c:: "real"
  shows "a*r^2 + b*r + c < 0 \<Longrightarrow>
    \<exists>y'> r. \<forall>x\<in>{r<..y'}. a*x^2 + b*x + c < 0"
  using quadratic_poly_eval continuity_lem_lt0 
  by (simp add: add.commute) 

lemma continuity_lem_gt0_expanded: 
  fixes r:: "real"
  fixes a b c:: "real"
  fixes k::"real"
  assumes kgt: "k > r"
  shows "a*r^2 + b*r + c > 0 \<Longrightarrow>
    \<exists>x\<in>{r<..k}. a*x^2 + b*x + c > 0"
proof -
  assume "a*r^2 + b*r + c > 0"
  then have "\<exists>y'> r. \<forall>x\<in>{r<..y'}. poly [:c, b, a:] x > 0"
    using continuity_lem_gt0 quadratic_poly_eval[of c b a r] by auto 
  then obtain y' where y_prop: "y' > r \<and> (\<forall>x\<in>{r<..y'}. poly [:c, b, a:] x > 0)" by auto
  then have "\<exists>q. q > r \<and> q < min k y'" using kgt dense
    by (metis min_less_iff_conj)   
  then obtain q where q_prop: "q > r \<and>q < min k y'" by auto
  then have "a*q^2 + b*q + c > 0" using y_prop  quadratic_poly_eval[of c b a q]
    by (metis greaterThanAtMost_iff less_eq_real_def min_less_iff_conj)
  then show ?thesis
    using q_prop by auto
qed

subsection "Negative Infinity (Limit) Properties"

lemma ysq_dom_y: 
  fixes b:: "real"
  fixes c:: "real"
  shows "\<exists>(w::real). \<forall>(y:: real). (y < w \<longrightarrow> y^2 > b*y)"
proof - 
  have c1: "b \<ge> 0 ==> \<exists>(w::real). \<forall>(y:: real). (y < w \<longrightarrow> y^2 > b*y)"
  proof - 
    assume "b \<ge> 0"
    then have p1: "\<forall>(y:: real). (y < -1 \<longrightarrow> y*b \<le> 0)"
      by (simp add: mult_nonneg_nonpos2)
    have p2: "\<forall>(y:: real). (y < -1 \<longrightarrow> y^2 > 0)"
      by auto 
    then have h1: "\<forall>(y:: real). (y < -1 \<longrightarrow> y^2 > b*y)"  
      using p1 p2
      by (metis less_eq_real_def less_le_trans mult.commute) 
    then show ?thesis by auto
  qed
  have c2: "b < 0 \<and> b > -1 ==> \<exists>(w::real). \<forall>(y:: real). (y < w \<longrightarrow> y^2 > b*y)"
  proof - 
    assume "b < 0 \<and> b > -1 "
    then have h1: "\<forall>(y:: real). (y < -1 \<longrightarrow> y^2 > b*y)"
      by (simp add: power2_eq_square)  
    then show ?thesis by auto
  qed   
  have c3: "b \<le> -1 ==> \<exists>(w::real). \<forall>(y:: real). (y < w \<longrightarrow> y^2 > b*y)"
  proof - 
    assume "b \<le> -1 "
    then have h1: "\<forall>(y:: real). (y < b \<longrightarrow> y^2 > b*y)"
      by (metis le_minus_one_simps(3) less_irrefl less_le_trans mult.commute mult_less_cancel_left power2_eq_square)
    then show ?thesis by auto
  qed   
  then  show ?thesis using c1 c2 c3
    by (metis less_trans linorder_not_less) 
qed

lemma ysq_dom_y_plus_coeff: 
  fixes b:: "real"
  fixes c:: "real"
  shows "\<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> y^2 > b*y + c)"
proof - 
  have "\<exists>(w::real). \<forall>(y:: real). (y < w \<longrightarrow> y^2 > b*y)" using ysq_dom_y by auto
  then obtain w where w_prop: "\<forall>(y:: real). (y < w \<longrightarrow> y^2 > b*y)" by auto
  have "c \<le> 0 \<Longrightarrow>  \<forall>(y::real). (y < w \<longrightarrow> y^2 > b*y + c)"
    using w_prop by auto 
  then have c1: "c \<le> 0 \<Longrightarrow> \<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> y^2 > b*y + c)" by auto
  have "\<exists>(w::real). \<forall>(y:: real). (y < w \<longrightarrow> y^2 > (b-c)*y)" using ysq_dom_y by auto
  then obtain k where k_prop: "\<forall>(y:: real). (y < k \<longrightarrow> y^2 > (b-c)*y)" by auto
  let ?mn = "min k (-1)"
  have "(c> 0 \<Longrightarrow> (\<forall> y < -1. -c*y > c))" 
  proof - 
    assume cgt: " c> 0"
    show "\<forall>(y::real) < -1. -c*y > c"
    proof clarsimp
      fix y::"real"
      assume "y < -1"
      then have "-y > 1"
        by auto
      then have "c < c*(-y)" using cgt 
        by (metis \<open>1 < - y\<close> mult.right_neutral mult_less_cancel_left_pos)
      then show " c < - (c * y) "
        by auto
    qed
  qed
  then have "(c> 0 \<longrightarrow> (\<forall> y < ?mn. (b-c)*y > b*y + c))" 
    by (simp add: left_diff_distrib) 
  then have c2:  "c > 0 \<Longrightarrow>  \<forall>(y::real). (y < ?mn \<longrightarrow> y^2 > b*y + c)"
    using k_prop
    by force
  then have c2:  "c > 0 \<Longrightarrow> \<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> y^2 > b*y + c)"
    by blast
  show ?thesis using c1 c2
    by fastforce
qed

lemma ysq_dom_y_plus_coeff_2: 
  fixes b:: "real"
  fixes c:: "real"
  shows "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> y^2 > b*y + c)"
proof - 
  have "\<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> y^2 > -b*y + c)"
    using ysq_dom_y_plus_coeff[where b = "-b", where c = "c"] by auto
  then obtain w where w_prop: "\<forall>(y::real). (y < w \<longrightarrow> y^2 > -b*y + c)" by auto
  let ?mn = "min w (-1)"
  have "\<forall>(y::real). (y < ?mn \<longrightarrow> y^2 > -b*y + c)" using w_prop by auto
  then have "\<forall>(y::real). (y > (-1*?mn) \<longrightarrow> y^2 > b*y + c)"
    by (metis (no_types, hide_lams) add.inverse_inverse minus_less_iff mult_minus1 mult_minus_left mult_minus_right power2_eq_square) 
  then show ?thesis by auto
qed

lemma neg_lc_dom_quad: 
  fixes a:: "real"
  fixes b:: "real"
  fixes c:: "real"
  assumes alt: "a < 0"
  shows "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> a*y^2 + b*y + c < 0)"
proof -
  have "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> y^2 > (-b/a)*y + (-c/a))"
    using ysq_dom_y_plus_coeff_2[where b = "-b/a", where c = "-c/a"] by auto
  then have keyh: "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> a*y^2 < a*((-b/a)*y + (-c/a)))"
    using alt by auto
  have simp1: "\<forall>y. a*((-b/a)*y + (-c/a)) = a*(-b/a)*y + a*(-c/a)"
    using diff_divide_eq_iff by fastforce
  have simp2: "\<forall>y. a*(-b/a)*y + a*(-c/a) = -b*y + a*(-c/a)"
    using assms by auto
  have simp3: "\<forall>y. -b*y + a*(-c/a) = -b*y - c"
    using assms by auto
  then have "\<forall>y. a*((-b/a)*y + (-c/a)) = -b*y - c" using simp1 simp2 simp3 by auto
  then have keyh2: "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> a*y^2 < -b*y-c)"
    using keyh by auto
  have "\<forall>y. a*y^2 < -b*y-c \<longleftrightarrow> a*y^2 + b*y + c < 0" by auto
  then show ?thesis using keyh2 by auto
qed

lemma pos_lc_dom_quad: 
  fixes a:: "real"
  fixes b:: "real"
  fixes c:: "real"
  assumes alt: "a > 0"
  shows "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> a*y^2 + b*y + c > 0)"
proof -
  have "-a < 0" using alt
    by simp 
  then have "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> -a*y^2 - b*y - c < 0)"
    using neg_lc_dom_quad[where a = "-a", where b = "-b", where c = "-c"] by auto
  then obtain w where w_prop: "\<forall>(y::real). (y > w \<longrightarrow> -a*y^2 - b*y - c < 0)" by auto
  then have "\<forall>(y::real). (y > w \<longrightarrow> a*y^2 + b*y + c > 0)"
    by auto
  then show ?thesis by auto
qed

(* lemma interval_infinite: 
  fixes r p::"real"
  assumes "r < p"
  shows "infinite {r<..<p}"
  using Set_Interval.dense_linorder_class.infinite_Ioo using assms by blast 
*)

subsection "Infinitesimal and Continuity Properties"
lemma les_qe_inf_helper: 
  fixes q:: "real"
  shows"(\<forall>(d, e, f)\<in>set les. \<exists>y'> q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f < 0) \<Longrightarrow> 
    (\<exists>y'>q. (\<forall>(d, e, f)\<in>set les. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f < 0))"
proof (induct les)
  case Nil
  then show ?case using gt_ex by auto 
next
  case (Cons z les)
  have "\<forall>a\<in>set les. case a of (d, e, f) \<Rightarrow> \<exists>y'>q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f < 0"
    using  Cons.prems by auto
  then have " \<exists>y'>q. \<forall>a\<in>set les. case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f < 0"
    using Cons.hyps by auto
  then obtain y1 where y1_prop : "y1>q \<and> (\<forall>a\<in>set les. case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..y1}. d * x\<^sup>2 + e * x + f < 0)"
    by auto
  have "case z of (d, e, f) \<Rightarrow> \<exists>y'>q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f < 0"
    using Cons.prems by auto
  then obtain y2 where y2_prop: "y2>q \<and> (case z of (d, e, f) \<Rightarrow> (\<forall>x\<in>{q<..y2}. d * x\<^sup>2 + e * x + f < 0))"
    by auto
  let ?y = "min y1 y2"
  have "?y > q \<and> (\<forall>a\<in>set (z#les). case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..?y}. d * x\<^sup>2 + e * x + f < 0)"
    using y1_prop y2_prop
    by force
  then show ?case
    by blast
qed 

lemma have_inbetween_point_les:
  fixes r::"real"
  assumes "(\<forall>(d, e, f)\<in>set les. \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0)"
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
proof -
  have "(\<forall>(d, e, f)\<in>set les. \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<Longrightarrow> 
    (\<exists>y'>r. (\<forall>(d, e, f)\<in>set les. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0))"
    using les_qe_inf_helper assms by auto
  then have "(\<exists>y'>r. (\<forall>(d, e, f)\<in>set les. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0))"
    using assms
    by blast 
  then obtain y where y_prop: "y > r \<and>  (\<forall>(d, e, f)\<in>set les. \<forall>x\<in>{r<..y}. d * x\<^sup>2 + e * x + f < 0)"
    by auto
  have "\<exists>q. q >  r \<and>q < y" using y_prop dense by auto
  then obtain q where q_prop: "q > r \<and> q < y" by auto
  then have "(\<forall>(d, e, f)\<in>set les. d*q^2 + e*q + f < 0)"
    using y_prop by auto
  then show ?thesis
    by auto
qed

lemma one_root_a_gt0: 
  fixes a b c r:: "real"
  shows "\<And>y'. b = 2 * a * r \<Longrightarrow>
          \<not> a < 0 \<Longrightarrow>
          a * r^2 - 2 * a *r*r + c = 0 \<Longrightarrow>
          - r < y' \<Longrightarrow>
          \<exists>x\<in>{-r<..y'}. \<not> a * x\<^sup>2 + 2 * a * r*x + c < 0"
proof - 
  fix y'
  assume beq: "b = 2 * a * r"
  assume aprop: " \<not> a < 0"
  assume root: " a * r\<^sup>2 - 2 * a *r*r + c = 0"
  assume rootlt: "- r < y'"
  show " \<exists>x\<in>{- r<..y'}. \<not> a * x\<^sup>2 + 2 * a* r*x+ c < 0"
  proof - 
    have h: "a = 0 \<Longrightarrow> (b = 0 \<and> c = 0)" using beq root   
      by auto
    then have aeq: "a = 0 \<Longrightarrow> \<exists>x\<in>{- r<..y'}. \<not> a * x\<^sup>2 + 2 * a*r*x + c < 0"
      using rootlt
      by (metis add.left_neutral continuity_lem_eq0 less_numeral_extra(3) mult_zero_left mult_zero_right) 
    then have alt: "a > 0 \<Longrightarrow> \<exists>x\<in>{- r<..y'}. \<not> a * x\<^sup>2 + 2 * a *r*x + c < 0"
    proof - 
      assume agt: "a > 0"
      then have "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> a*y^2 + b*y + c > 0)"
        using pos_lc_dom_quad by auto
      then obtain w where w_prop: "\<forall>y::real. (y > w \<longrightarrow> a*y^2 + b*y + c > 0)" by auto
      have isroot: "a*(-r)^2 + b*(-r) + c = 0" using root beq by auto
      then have wgteq: "w \<ge> -(r)"
      proof -
        have "w < -r \<Longrightarrow> False"
          using w_prop isroot by auto
        then show ?thesis
          using not_less by blast 
      qed
      then have w1: "w + 1 > -r"
        by auto 
      have w2: "a*(w + 1)^2 + b*(w+1) + c > 0" using w_prop by auto
      have rootiff: "\<forall>x. a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> x = -r" using  discriminant_lemma[where a = "a", where b = "b", where c= "c", where r = "r"]
          isroot agt beq by auto
      have allgt: "\<forall>x > -r. a*x^2 + b*x + c > 0"
      proof clarsimp 
        fix x
        assume "x > -r"
        have xgtw:  "x > w + 1 \<Longrightarrow> a*x^2 + b*x + c > 0 "
          using w1 w2 rootiff  poly_IVT_neg[where a = "w+1", where b = "x", where p = "[:c,b,a:]"] 
            quadratic_poly_eval
          by (metis less_eq_real_def linorder_not_less) 
        have xltw: "x < w + 1 \<Longrightarrow> a*x^2 + b*x + c > 0"
          using w1 w2 rootiff poly_IVT_pos[where a= "x", where b = "w + 1", where p = "[:c,b,a:]"]
            quadratic_poly_eval less_eq_real_def linorder_not_less
          by (metis \<open>- r < x\<close>)
        then show "a*x^2 + b*x + c > 0"
          using w2 xgtw xltw by fastforce 
      qed
      have "\<exists>z. z > -r \<and> z < y'" using rootlt dense[where x = "-r", where y = "y'"] 
        by auto
      then obtain z where z_prop: " z > -r \<and> z  < y'" by auto
      then have "a*z^2 + b*z + c > 0" using allgt by auto
      then show ?thesis using z_prop
        using beq greaterThanAtMost_iff by force 
    qed
    then show ?thesis using aeq alt aprop
      by linarith
  qed
qed

lemma leq_qe_inf_helper: 
  fixes q:: "real"
  shows"(\<forall>(d, e, f)\<in>set leq. \<exists>y'> q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<Longrightarrow> 
    (\<exists>y'>q. (\<forall>(d, e, f)\<in>set leq. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<le> 0))"
proof (induct leq)
  case Nil
  then show ?case using gt_ex by auto 
next
  case (Cons z leq)
  have "\<forall>a\<in>set leq. case a of (d, e, f) \<Rightarrow> \<exists>y'>q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<le> 0"
    using  Cons.prems by auto
  then have " \<exists>y'>q. \<forall>a\<in>set leq. case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<le> 0"
    using Cons.hyps by auto
  then obtain y1 where y1_prop : "y1>q \<and> (\<forall>a\<in>set leq. case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..y1}. d * x\<^sup>2 + e * x + f \<le> 0)"
    by auto
  have "case z of (d, e, f) \<Rightarrow> \<exists>y'>q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<le> 0"
    using Cons.prems by auto
  then obtain y2 where y2_prop: "y2>q \<and> (case z of (d, e, f) \<Rightarrow> (\<forall>x\<in>{q<..y2}. d * x\<^sup>2 + e * x + f \<le> 0))"
    by auto
  let ?y = "min y1 y2"
  have "?y > q \<and> (\<forall>a\<in>set (z#leq). case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..?y}. d * x\<^sup>2 + e * x + f \<le> 0)"
    using y1_prop y2_prop
    by force
  then show ?case
    by blast
qed 

lemma neq_qe_inf_helper: 
  fixes q:: "real"
  shows"(\<forall>(d, e, f)\<in>set neq. \<exists>y'> q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<Longrightarrow> 
    (\<exists>y'>q. (\<forall>(d, e, f)\<in>set neq. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
proof (induct neq)
  case Nil
  then show ?case using gt_ex by auto 
next
  case (Cons z neq)
  have "\<forall>a\<in>set neq. case a of (d, e, f) \<Rightarrow> \<exists>y'>q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0"
    using  Cons.prems by auto
  then have " \<exists>y'>q. \<forall>a\<in>set neq. case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0"
    using Cons.hyps by auto
  then obtain y1 where y1_prop : "y1>q \<and> (\<forall>a\<in>set neq. case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..y1}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
    by auto
  have "case z of (d, e, f) \<Rightarrow> \<exists>y'>q. \<forall>x\<in>{q<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0"
    using Cons.prems by auto
  then obtain y2 where y2_prop: "y2>q \<and> (case z of (d, e, f) \<Rightarrow> (\<forall>x\<in>{q<..y2}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
    by auto
  let ?y = "min y1 y2"
  have "?y > q \<and> (\<forall>a\<in>set (z#neq). case a of (d, e, f) \<Rightarrow> \<forall>x\<in>{q<..?y}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
    using y1_prop y2_prop
    by force
  then show ?case
    by blast
qed 


subsection "Some Casework"

lemma quadratic_shape1a:
  fixes a b c x y::"real"
  assumes agt: "a > 0"
  assumes xyroots: "x < y \<and> a*x^2 + b*x + c = 0 \<and> a*y^2 + b*y + c = 0"
  shows "\<And>z. (z > x \<and> z < y \<Longrightarrow> a*z^2 + b*z + c < 0)"
proof clarsimp 
  fix z
  assume zgt: "z > x"
  assume zlt: "z < y"
  have frac_gtz: "(1/(2*a)) > 0" using agt
    by simp 
  have xy_prop:"(x = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> y = (-b - sqrt(b^2 - 4*a*c))/(2*a))
    \<or> (y = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> x = (-b - sqrt(b^2 - 4*a*c))/(2*a))" 
    using xyroots agt discriminant_iff unfolding discrim_def by auto   
  have "b^2 - 4*a*c \<ge> 0" using xyroots discriminant_iff
    using assms(1) discrim_def by auto 
  then have pos_discrim: "b^2 - 4*a*c > 0" using xyroots discriminant_zero
    using \<open>0 \<le> b\<^sup>2 - 4 * a * c\<close> assms(1) discrim_def less_eq_real_def linorder_not_less
    by metis
  then have sqrt_gt: "sqrt(b^2 - 4*a*c) > 0"
    using real_sqrt_gt_0_iff by blast 
  then have "(- b - sqrt(b^2 - 4*a*c)) < (- b + sqrt(b^2 - 4*a*c))"
    by auto
  then have "(- b - sqrt(b^2 - 4*a*c))*(1/(2*a)) < (- b + sqrt(b^2 - 4*a*c))*(1/(2*a)) "
    using frac_gtz
    by (simp add: divide_strict_right_mono) 
  then have "(- b - sqrt(b^2 - 4*a*c))/(2*a) < (- b + sqrt(b^2 - 4*a*c))/(2*a)"
    by auto
  then have xandy: "x = (- b - sqrt(b^2 - 4*a*c))/(2*a) \<and> y = (- b + sqrt(b^2 - 4*a*c))/(2*a)"
    using xy_prop xyroots by auto
  let ?mdpt = "-b/(2*a)"
  have xlt: "x < ?mdpt"
    using xandy sqrt_gt using frac_gtz divide_minus_left divide_strict_right_mono sqrt_gt
    by (smt (verit) agt)
  have ylt: "?mdpt < y"
    using xandy sqrt_gt frac_gtz
    by (smt (verit, del_insts) divide_strict_right_mono zero_less_divide_1_iff) 
  have mdpt_val: "a*?mdpt^2 + b*?mdpt + c < 0"
  proof - 
    have firsteq: "a*?mdpt^2 + b*?mdpt + c = (a*b^2)/(4*a^2) - (b^2)/(2*a) + c"
      by (simp add: power2_eq_square) 
    have h1: "(a*b^2)/(4*a^2) = (b^2)/(4*a)"
      by (simp add: power2_eq_square)
    have h2: "(b^2)/(2*a) = (2*b^2)/(4*a)"
      by linarith
    have h3: "c = (4*a*c)/(4*a)"
      using agt by auto 
    have "a*?mdpt^2 + b*?mdpt + c = (b^2)/(4*a) - (2*b^2)/(4*a) + (4*a*c)/(4*a) "
      using firsteq h1 h2 h3
      by linarith 
    then have "a*?mdpt^2 + b*?mdpt + c = (b^2 - 2*b^2 + 4*a*c)/(4*a)"
      by (simp add: diff_divide_distrib)
    then have eq2: "a*?mdpt^2 + b*?mdpt + c = (4*a*c - b^2)/(4*a)"
      by simp
    have h: "4*a*c - b^2 < 0" using pos_discrim by auto
    have "1/(4*a) > 0" using agt by auto
    then have "(4*a*c - b^2)*(1/(4*a)) < 0"
      using h
      using mult_less_0_iff by blast 
    then show ?thesis using eq2 by auto
  qed
  have nex: "\<not> (\<exists>k> x. k < y \<and> poly [:c, b, a:] k = 0)"
    using discriminant_iff agt
    by (metis (no_types, hide_lams) discrim_def order_less_irrefl quadratic_poly_eval xandy) 
  have nor2: "\<not> (\<exists>x>z. x < - b / (2 * a) \<and> poly [:c, b, a:] x = 0)"
    using nex xlt ylt zgt zlt by auto
  have nor: "\<not> (\<exists>x>- b / (2 * a). x < z \<and> poly [:c, b, a:] x = 0)"
    using nex xlt ylt zgt zlt discriminant_iff agt  by auto 
  then have mdpt_lt: "?mdpt < z \<Longrightarrow> a*z^2 + b*z + c < 0 "
    using mdpt_val zgt zlt xlt ylt poly_IVT_pos[where p = "[:c, b, a:]", where a= "?mdpt", where b = "z"] 
      quadratic_poly_eval[of c b a]
    by (metis \<open>\<not> (\<exists>k>x. k < y \<and> poly [:c, b, a:] k = 0)\<close> linorder_neqE_linordered_idom) 
  have mdpt_gt: "?mdpt > z \<Longrightarrow> a*z^2 + b*z + c < 0 "
    using zgt zlt mdpt_val xlt ylt nor2 poly_IVT_neg[where p = "[:c, b, a:]", where a = "z", where b = "?mdpt"] quadratic_poly_eval[of c b a]
    by (metis linorder_neqE_linordered_idom nex) 
  then show "a*z^2 + b*z + c < 0" 
    using mdpt_lt mdpt_gt mdpt_val by fastforce 
qed

lemma quadratic_shape1b:
  fixes a b c x y::"real"
  assumes agt: "a > 0"
  assumes xy_roots: "x < y \<and> a*x^2 + b*x + c = 0 \<and> a*y^2 + b*y + c = 0"
  shows "\<And>z. (z > y \<Longrightarrow> a*z^2 + b*z + c > 0)"
proof - 
  fix z
  assume z_gt :"z > y"
  have nogt: "\<not>(\<exists>w. w > y \<and> a*w^2 + b*w + c = 0)" using xy_roots discriminant_iff
    by (metis agt less_eq_real_def linorder_not_less)
  have "\<exists>(w::real). \<forall>(y::real). (y > w \<longrightarrow> a*y^2 + b*y + c > 0)"
    using agt pos_lc_dom_quad by auto
  then have "\<exists>k > y.  a*k^2 + b*k + c > 0"
    by (metis add.commute agt less_add_same_cancel1 linorder_neqE_linordered_idom pos_add_strict) 
  then obtain k where k_prop: "k > y \<and> a*k^2 + b*k + c > 0" by auto
  have kgt: "k > z \<Longrightarrow> a*z^2 + b*z + c > 0" 
  proof - 
    assume kgt: "k > z"
    then have zneq: "a*z^2 + b*z + c = 0 \<Longrightarrow> False"
      using nogt  using z_gt by blast 
    have znlt: "a*z^2 + b*z + c < 0 \<Longrightarrow> False"
      using kgt k_prop quadratic_poly_eval[of c b a] z_gt  nogt poly_IVT_pos[where a= "z", where b = "k", where p = "[:c, b, a:]"]
      by (metis less_eq_real_def less_le_trans)
    then show "a*z^2 + b*z + c > 0" using zneq znlt
      using linorder_neqE_linordered_idom by blast 
  qed
  have klt: "k < z \<Longrightarrow> a*z^2 + b*z + c > 0" 
  proof - 
    assume klt: "k < z"
    then have zneq: "a*z^2 + b*z + c = 0 \<Longrightarrow> False"
      using nogt using z_gt by blast 
    have znlt: "a*z^2 + b*z + c < 0 \<Longrightarrow> False"
      using klt k_prop quadratic_poly_eval[of c b a] z_gt  nogt poly_IVT_neg[where a= "k", where b = "z", where p = "[:c, b, a:]"]
      by (metis add.commute add_less_cancel_left add_mono_thms_linordered_field(3) less_eq_real_def)
    then show "a*z^2 + b*z + c > 0" using zneq znlt
      using linorder_neqE_linordered_idom by blast 
  qed
  then show "a*z^2 + b*z + c > 0" using k_prop kgt klt
    by fastforce 
qed

lemma quadratic_shape2a:
  fixes a b c x y::"real"
  assumes "a < 0"
  assumes "x < y \<and> a*x^2 + b*x + c = 0 \<and> a*y^2 + b*y + c = 0"
  shows "\<And>z. (z > x \<and> z < y \<Longrightarrow> a*z^2 + b*z + c > 0)"
  using quadratic_shape1a[where a= "-a", where b = "-b", where c = "-c", where x = "x", where y = "y"]
  using assms(1) assms(2) by fastforce 

lemma quadratic_shape2b:
  fixes a b c x y::"real"
  assumes "a < 0"
  assumes "x < y \<and> a*x^2 + b*x + c = 0 \<and> a*y^2 + b*y + c = 0"
  shows "\<And>z. (z > y \<Longrightarrow> a*z^2 + b*z + c < 0)"
  using quadratic_shape1b[where a= "-a", where b = "-b", where c = "-c", where x = "x", where y = "y"]
  using assms(1) assms(2) by force 

lemma case_d1:
  fixes a b c r::"real"
  shows "b < 2 * a * r \<Longrightarrow>
    a * r^2 - b*r + c = 0 \<Longrightarrow>
    \<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c < 0"
proof - 
  assume b_lt: "b < 2*a*r"
  assume root: "a*r^2 - b*r + c = 0"
  then have "c = b*r - a*r^2" by auto
  have aeq: "a = 0 \<Longrightarrow> \<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c < 0"
  proof - 
    assume azer: "a = 0"
    then have bltz: "b < 0" using b_lt by auto
    then have "c = b*r" using azer root by auto
    then have eval: "\<forall>x. a*x^2 + b*x + c = b*(x + r)" using azer
      by (simp add: distrib_left) 
    have "\<forall>x > -r. b*(x + r) < 0" 
    proof clarsimp 
      fix x
      assume xgt: "- r < x"
      then have "x + r > 0"
        by linarith 
      then show "b * (x + r) < 0"
        using bltz using mult_less_0_iff by blast 
    qed
    then show ?thesis using eval
      using less_add_same_cancel1 zero_less_one
      by (metis greaterThanAtMost_iff)
  qed
  have aneq: "a \<noteq> 0 \<Longrightarrow>\<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c < 0"
  proof - 
    assume aneq: "(a::real) \<noteq> 0"
    have "b^2 - 4*a*c < 0 \<Longrightarrow> a * r\<^sup>2 + b * r + c \<noteq> 0" using root discriminant_negative[of a b c r] unfolding discrim_def 
      using aneq by auto
    then have " a * r\<^sup>2 + b * r + c \<noteq> 0 \<Longrightarrow>
    a * r\<^sup>2 - b * r + c = 0 \<Longrightarrow>
    b\<^sup>2 < 4 * a * c \<Longrightarrow> False"
    proof -
      assume a1: "a * r\<^sup>2 - b * r + c = 0"
      assume a2: "b\<^sup>2 < 4 * a * c"
      have f3: "(0 \<le> - 1 * (4 * a * c) + (- 1 * b)\<^sup>2) = (4 * a * c + - 1 * (- 1 * b)\<^sup>2 \<le> 0)"
        by simp
      have f4: "(- 1 * b)\<^sup>2 + - 1 * (4 * a * c) = - 1 * (4 * a * c) + (- 1 * b)\<^sup>2"
        by auto
      have f5: "c + a * r\<^sup>2 + - 1 * b * r = a * r\<^sup>2 + c + - 1 * b * r"
        by auto
      have f6: "\<forall>x0 x1 x2 x3. (x3::real) * x0\<^sup>2 + x2 * x0 + x1 = x1 + x3 * x0\<^sup>2 + x2 * x0"
        by simp
      have f7: "\<forall>x1 x2 x3. (discrim x3 x2 x1 < 0) = (\<not> 0 \<le> discrim x3 x2 x1)"
        by auto
      have f8: "\<forall>r ra rb. discrim r ra rb = ra\<^sup>2 + - 1 * (4 * r * rb)"
        using discrim_def by auto
      have "\<not> 4 * a * c + - 1 * (- 1 * b)\<^sup>2 \<le> 0"
        using a2 by simp
      then have "a * r\<^sup>2 + c + - 1 * b * r \<noteq> 0"
        using f8 f7 f6 f5 f4 f3 by (metis (no_types) aneq discriminant_negative)
      then show False
        using a1 by linarith
    qed 
    then have "\<not>(b^2 - 4*a*c < 0)" using root
      using \<open>b\<^sup>2 - 4 * a * c < 0 \<Longrightarrow> a * r\<^sup>2 + b * r + c \<noteq> 0\<close> by auto
    then have discrim: "b\<^sup>2 \<ge> 4 * a * c " by auto
    then have req: "r = (b + sqrt(b^2 - 4*a*c))/(2*a) \<or> r = (b - sqrt(b^2 - 4*a*c))/(2*a)"
      using aneq root discriminant_iff[where a="a", where b ="-b", where c="c", where x="r"] unfolding discrim_def
      by auto
    then have "r = (b - sqrt(b^2 - 4*a*c))/(2*a) \<Longrightarrow> b > 2*a*r"
    proof - 
      assume req: "r = (b - sqrt(b^2 - 4*a*c))/(2*a)"
      then have h1: "2*a*r = 2*a*((b - sqrt(b^2 - 4*a*c))/(2*a))" by auto
      then have h2: "2*a*((b - sqrt(b^2 - 4*a*c))/(2*a)) = b - sqrt(b^2 - 4*a*c)"
        using aneq by auto
      have h3: "sqrt(b^2 - 4*a*c) \<ge> 0" using discrim  by auto
      then have "b - sqrt(b^2 - 4*a*c) < b"
        using b_lt h1 h2 by linarith
      then show ?thesis using req h2 by auto
    qed
    then have req: "r = (b + sqrt(b^2 - 4*a*c))/(2*a)" using req b_lt by auto
    then have discrim2: "b^2 - 4 *a*c > 0" using aneq b_lt  by auto
    then have "\<exists>x y. x \<noteq> y \<and> a * x\<^sup>2 + b * x + c = 0 \<and> a * y\<^sup>2 + b * y + c = 0"
      using aneq discriminant_pos_ex[of a b c] unfolding discrim_def
      by auto
    then obtain x y where xy_prop: "x < y \<and> a * x\<^sup>2 + b * x + c = 0 \<and> a * y\<^sup>2 + b * y + c = 0"
      by (meson linorder_neqE_linordered_idom)
    then have "(x = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> y = (-b - sqrt(b^2 - 4*a*c))/(2*a))
\<or> (y = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> x = (-b - sqrt(b^2 - 4*a*c))/(2*a))" 
      using aneq discriminant_iff unfolding discrim_def by auto   
    then have xy_prop2: "(x = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> y = -r)
    \<or> (y = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> x = -r)" using req
      by (simp add: \<open>x = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> y = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<or> y = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> x = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> minus_divide_left)
        (* When a < 0, -r is the bigger root *)
    have alt: "a < 0 \<Longrightarrow> \<forall>k > -r. a * k^2 + b * k + c < 0"
    proof clarsimp 
      fix k
      assume alt: " a < 0"
      assume "- r < k"
      have alt2: " (1/(2*a)::real) < 0" using alt
        by simp 
      have "(-b - sqrt(b^2 - 4*a*c)) < (-b + sqrt(b^2 - 4*a*c))"
        using discrim2 by auto
      then have "(-b - sqrt(b^2 - 4*a*c))* (1/(2*a)::real) > (-b + sqrt(b^2 - 4*a*c))* (1/(2*a)::real)"
        using alt2
        using mult_less_cancel_left_neg by fastforce 
      then have rgtroot: "-r >  (-b + sqrt(b^2 - 4*a*c))/(2*a)"
        using req  \<open>x = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> y = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<or> y = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> x = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> xy_prop2
        by auto 
      then have "(y = -r \<and> x = (-b + sqrt(b^2 - 4*a*c))/(2*a))"
        using xy_prop xy_prop2 by auto
      then show "a * k^2 + b * k + c < 0"
        using xy_prop \<open>- r < k\<close> alt quadratic_shape2b xy_prop 
        by blast 
    qed
      (* When a > 0, -r is the smaller root *)
    have agt: "a > 0 \<Longrightarrow> \<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c < 0"
    proof - 
      assume agt: "a> 0"
      have alt2: " (1/(2*a)::real) > 0" using agt
        by simp 
      have "(-b - sqrt(b^2 - 4*a*c)) < (-b + sqrt(b^2 - 4*a*c))"
        using discrim2 by auto
      then have "(-b - sqrt(b^2 - 4*a*c))* (1/(2*a)::real) < (-b + sqrt(b^2 - 4*a*c))* (1/(2*a)::real)"
        using alt2
      proof -
        have f1: "- b - sqrt (b\<^sup>2 - c * (4 * a)) < - b + sqrt (b\<^sup>2 - c * (4 * a))"
          by (metis \<open>- b - sqrt (b\<^sup>2 - 4 * a * c) < - b + sqrt (b\<^sup>2 - 4 * a * c)\<close> mult.commute)
        have "0 < a * 2"
          using \<open>0 < 1 / (2 * a)\<close> by auto
        then show ?thesis
          using f1 by (simp add: divide_strict_right_mono mult.commute)
      qed
      then have rlltroot: "-r <  (-b + sqrt(b^2 - 4*a*c))/(2*a)"
        using req \<open>x = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> y = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<or> y = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> x = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> xy_prop2
        by auto
      then have "(x = -r \<and> y = (-b + sqrt(b^2 - 4*a*c))/(2*a))"
        using xy_prop xy_prop2 by auto
      have "\<exists>k. x < k \<and> k < y" using xy_prop dense by auto
      then obtain k where k_prop: "x < k \<and> k < y" by auto
      then have "\<forall>x\<in>{-r<..k}. a * x\<^sup>2 + b * x + c < 0"
        using agt quadratic_shape1a[where a= "a", where b = "b", where c= "c", where x = "x", where y = "y"]
        using \<open>x = - r \<and> y = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> greaterThanAtMost_iff xy_prop by auto 
      then show "\<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c < 0" 
        using k_prop using \<open>x = - r \<and> y = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> by blast 
    qed
    show ?thesis
      using alt agt
      by (metis aneq greaterThanAtMost_iff less_add_same_cancel1 linorder_neqE_linordered_idom zero_less_one) 
  qed
  show "\<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c < 0" using aeq aneq
    by blast 
qed

lemma case_d4:
  fixes a b c r::"real"
  shows "\<And>y'. b \<noteq> 2 * a * r \<Longrightarrow>
          \<not> b < 2 * a * r \<Longrightarrow>
          a *r^2 - b * r + c = 0 \<Longrightarrow>
          -r < y' \<Longrightarrow> \<exists>x\<in>{-r<..y'}. \<not> a * x\<^sup>2 + b * x + c < 0"
proof - 
  fix y'
  assume bneq: "b \<noteq> 2 * a * r"
  assume bnotless: "\<not> b < 2 * a * r"
  assume root: "a *r^2 - b * r + c = 0"
  assume y_prop: "-r < y'"
  have b_gt: "b > 2*a*r" using bneq bnotless by auto
  have aeq: "a = 0 \<Longrightarrow> \<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c > 0"
  proof - 
    assume azer: "a = 0"
    then have bgt: "b > 0" using b_gt by auto
    then have "c = b*r" using azer root by auto
    then have eval: "\<forall>x. a*x^2 + b*x + c = b*(x + r)" using azer
      by (simp add: distrib_left) 
    have "\<forall>x > -r. b*(x + r) > 0" 
    proof clarsimp 
      fix x
      assume xgt: "- r < x"
      then have "x + r > 0"
        by linarith 
      then show "b * (x + r) > 0"
        using bgt by auto 
    qed
    then show ?thesis using eval 
      using less_add_same_cancel1 zero_less_one
      by (metis greaterThanAtMost_iff) 
  qed
  have aneq: "a \<noteq> 0 \<Longrightarrow>\<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c > 0"
  proof - 
    assume aneq: "a\<noteq>0"  
    {
      assume a1: "a * r\<^sup>2 - b * r + c = 0"
      assume a2: "b\<^sup>2 < 4 * a * c"
      have f3: "(0 \<le> - 1 * (4 * a * c) + (- 1 * b)\<^sup>2) = (4 * a * c + - 1 * (- 1 * b)\<^sup>2 \<le> 0)"
        by simp
      have f4: "(- 1 * b)\<^sup>2 + - 1 * (4 * a * c) = - 1 * (4 * a * c) + (- 1 * b)\<^sup>2"
        by auto
      have f5: "c + a * r\<^sup>2 + - 1 * b * r = a * r\<^sup>2 + c + - 1 * b * r"
        by auto
      have f6: "\<forall>x0 x1 x2 x3. (x3::real) * x0\<^sup>2 + x2 * x0 + x1 = x1 + x3 * x0\<^sup>2 + x2 * x0"
        by simp
      have f7: "\<forall>x1 x2 x3. (discrim x3 x2 x1 < 0) = (\<not> 0 \<le> discrim x3 x2 x1)"
        by auto
      have f8: "\<forall>r ra rb. discrim r ra rb = ra\<^sup>2 + - 1 * (4 * r * rb)"
        using discrim_def by auto
      have "\<not> 4 * a * c + - 1 * (- 1 * b)\<^sup>2 \<le> 0"
        using a2 by simp
      then have "a * r\<^sup>2 + c + - 1 * b * r \<noteq> 0"
        using f8 f7 f6 f5 f4 f3 by (metis (no_types) aneq discriminant_negative)
      then have False
        using a1 by linarith
    } note * = this
    have "b^2 - 4*a*c < 0 \<Longrightarrow> a * r\<^sup>2 + b * r + c \<noteq> 0" using root discriminant_negative[of a b c r] unfolding discrim_def 
      using aneq by auto
    then have "\<not>(b^2 - 4*a*c < 0)" using root * by auto
    then have discrim: "b\<^sup>2 \<ge> 4 * a * c " by auto
    then have req: "r = (b + sqrt(b^2 - 4*a*c))/(2*a) \<or> r = (b - sqrt(b^2 - 4*a*c))/(2*a)"
      using aneq root discriminant_iff[where a="a", where b ="-b", where c="c", where x="r"] unfolding discrim_def
      by auto
    then have "r = (b + sqrt(b^2 - 4*a*c))/(2*a) \<Longrightarrow> b < 2*a*r"
    proof - 
      assume req: "r = (b + sqrt(b^2 - 4*a*c))/(2*a)"
      then have h1: "2*a*r = 2*a*((b + sqrt(b^2 - 4*a*c))/(2*a))" by auto
      then have h2: "2*a*((b + sqrt(b^2 - 4*a*c))/(2*a)) = b + sqrt(b^2 - 4*a*c)"
        using aneq by auto
      have h3: "sqrt(b^2 - 4*a*c) \<ge> 0" using discrim  by auto
      then have "b + sqrt(b^2 - 4*a*c) > b"
        using b_gt h1 h2 by linarith
      then show ?thesis using req h2 by auto
    qed
    then have req: "r = (b - sqrt(b^2 - 4*a*c))/(2*a)" using req b_gt
      using aneq discrim by auto
    then have discrim2: "b^2 - 4 *a*c > 0" using aneq b_gt  by auto
    then have "\<exists>x y. x \<noteq> y \<and> a * x\<^sup>2 + b * x + c = 0 \<and> a * y\<^sup>2 + b * y + c = 0"
      using aneq discriminant_pos_ex[of a b c] unfolding discrim_def
      by auto
    then obtain x y where xy_prop: "x < y \<and> a * x\<^sup>2 + b * x + c = 0 \<and> a * y\<^sup>2 + b * y + c = 0"
      by (meson linorder_neqE_linordered_idom)
    then have "(x = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> y = (-b - sqrt(b^2 - 4*a*c))/(2*a))
\<or> (y = (-b + sqrt(b^2 - 4*a*c))/(2*a) \<and> x = (-b - sqrt(b^2 - 4*a*c))/(2*a))" 
      using aneq discriminant_iff unfolding discrim_def by auto   
    then have xy_prop2: "(x = (-b - sqrt(b^2 - 4*a*c))/(2*a) \<and> y = -r)
    \<or> (y = (-b - sqrt(b^2 - 4*a*c))/(2*a) \<and> x = -r)" using req divide_inverse minus_diff_eq mult.commute mult_minus_right
      by (smt (verit, ccfv_SIG) uminus_add_conv_diff)
        (* When a > 0, -r is the greater root *)
    have agt: "a > 0 \<Longrightarrow> \<forall>k > -r. a * k^2 + b * k + c > 0"
    proof clarsimp 
      fix k
      assume agt: " a > 0"
      assume "- r < k"
      have agt2: " (1/(2*a)::real) > 0" using agt
        by simp 
      have "(-b - sqrt(b^2 - 4*a*c)) < (-b + sqrt(b^2 - 4*a*c))"
        using discrim2 by auto
      then have "(-b - sqrt(b^2 - 4*a*c))* (1/(2*a)::real) < (-b + sqrt(b^2 - 4*a*c))* (1/(2*a)::real)"
        using agt2 by (simp add: divide_strict_right_mono) 
      then have rgtroot: "-r >  (-b - sqrt(b^2 - 4*a*c))/(2*a)"
        using  req \<open>x = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> y = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<or> y = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> x = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> xy_prop2
        by auto 
      then have "(x = (-b - sqrt(b^2 - 4*a*c))/(2*a)) \<and> y = -r"
        using xy_prop xy_prop2 
        by auto
      then show "a * k^2 + b * k + c > 0"
        using \<open>- r < k\<close> xy_prop agt quadratic_shape1b[where a= "a", where b ="b", where c="c", where x = "x", where y = "-r", where z = "k"]    
        by blast 
    qed
      (* When a < 0, -r is the smaller root *)
    have agt2: "a < 0 \<Longrightarrow> \<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c > 0"
    proof - 
      assume alt: "a<0"
      have alt2: " (1/(2*a)::real) < 0" using alt
        by simp 
      have "(-b - sqrt(b^2 - 4*a*c)) < (-b + sqrt(b^2 - 4*a*c))"
        using discrim2 by auto
      then have "(-b - sqrt(b^2 - 4*a*c))* (1/(2*a)::real) > (-b + sqrt(b^2 - 4*a*c))* (1/(2*a)::real)"
        using alt2  using mult_less_cancel_left_neg by fastforce 
      then have rlltroot: "-r < (-b - sqrt(b^2 - 4*a*c))/(2*a)"
        using req 
        using \<open>x = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> y = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<or> y = (- b + sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) \<and> x = (- b - sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)\<close> 
          xy_prop2 
        by auto
      then have h: "(x = -r \<and> y = (-b - sqrt(b^2 - 4*a*c))/(2*a))"
        using xy_prop xy_prop2 
        by auto
      have "\<exists>k. x < k \<and> k < y" using xy_prop dense by auto
      then obtain k where k_prop: "x < k \<and> k < y" by auto
      then have "\<forall>x\<in>{-r<..k}. a * x\<^sup>2 + b * x + c > 0"
        using alt quadratic_shape2a[where a= "a", where b = "b", where c= "c", where x = "x", where y = "y"]
          xy_prop  h greaterThanAtMost_iff  by auto 
      then show "\<exists>y'>- r. \<forall>x\<in>{-r<..y'}. a * x\<^sup>2 + b * x + c > 0" 
        using k_prop using h by blast 
    qed
    show ?thesis
      using aneq agt agt2
      by (meson greaterThanAtMost_iff linorder_neqE_linordered_idom y_prop) 
  qed
  show "\<exists>x\<in>{-r<..y'}. \<not> a * x\<^sup>2 + b * x + c < 0" using aneq aeq
    by (metis greaterThanAtMost_iff less_eq_real_def linorder_not_less y_prop)
qed

lemma one_root_a_lt0:
  fixes a b c r y'::"real"
  assumes alt: "a < 0"
  assumes beq: "b = 2 * a * r"
  assumes root: " a * r^2 - 2*a*r*r + c = 0"
  shows "\<exists>y'>- r. \<forall>x\<in>{- r<..y'}. a * x\<^sup>2 + 2*a*r*x + c < 0"
proof - 
  have root_iff: "\<forall>x. a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> x = -r" using alt root discriminant_lemma[where r = "r"] beq 
    by auto
  have "a < 0 \<longrightarrow> (\<exists>y. \<forall>x > y. a*x^2 + b*x + c < 0)" using neg_lc_dom_quad 
    by auto
  then obtain k where k_prop: "\<forall>x > k. a*x^2 + b*x + c < 0" using alt by auto
  let ?mx = "max (k+1) (-r + 1)"
  have "a*?mx^2 + b*?mx + c < 0" using k_prop by auto
  then have "\<exists>y > -r. a*y^2 + b*y + c < 0"
    by force
  then obtain z where z_prop: "z > -r \<and> a*z^2 + b*z + c < 0" by auto
  have poly_eval_prop: "\<forall>(x::real). poly [:c, b, a :] x = a*x^2 + b*x + c" 
    using quadratic_poly_eval by auto
  then have nozer: "\<not>(\<exists>x. (x > -r \<and> poly [:c, b, a :] x = 0))" using root_iff 
    by (simp add: add.commute) 
  have poly_z: "poly [:c, b, a:] z < 0" using z_prop poly_eval_prop by auto
  have "\<forall>y > -r. a*y^2 + b*y + c < 0" 
  proof clarsimp 
    fix y
    assume ygt: "- r < y"
    have h1: "y = z \<Longrightarrow> a * y\<^sup>2 + b * y + c < 0" using z_prop by auto
    have h2: "y < z \<Longrightarrow> a * y\<^sup>2 + b * y + c < 0" proof -
      assume ylt: "y < z"
      have notz: "a*y^2 + b*y + c \<noteq> 0" using ygt nozer poly_eval_prop by auto
      have h1: "a *y^2 + b*y + c > 0 \<Longrightarrow> poly [:c, b, a:] y > 0" using poly_eval_prop by auto
      have ivtprop: "poly [:c, b, a:] y > 0 \<Longrightarrow> (\<exists>x. y < x \<and> x < z \<and> poly [:c, b, a:] x = 0)" 
        using ylt poly_z poly_IVT_neg[where a = "y", where b = "z", where p = "[:c, b, a:]"]
        by auto
      then have "a*y^2 + b*y + c > 0 \<Longrightarrow> False" using h1 ivtprop ygt nozer by auto
      then show "a*y^2 + b*y + c < 0" using notz
        using linorder_neqE_linordered_idom by blast 
    qed
    have h3: "y > z \<Longrightarrow> a * y\<^sup>2 + b * y + c < 0" 
    proof -
      assume ygtz: "y > z"
      have notz: "a*y^2 + b*y + c \<noteq> 0" using ygt nozer poly_eval_prop by auto
      have h1: "a *y^2 + b*y + c > 0 \<Longrightarrow> poly [:c, b, a:] y > 0" using poly_eval_prop by auto
      have ivtprop: "poly [:c, b, a:] y > 0 \<Longrightarrow> (\<exists>x. z < x \<and> x < y \<and> poly [:c, b, a:] x = 0)" 
        using ygtz poly_z using poly_IVT_pos by blast 
      then have "a*y^2 + b*y + c > 0 \<Longrightarrow> False" using h1 ivtprop z_prop nozer by auto
      then show "a*y^2 + b*y + c < 0" using notz
        using linorder_neqE_linordered_idom by blast 
    qed
    show "a * y\<^sup>2 + b * y + c < 0" using h1 h2 h3
      using linorder_neqE_linordered_idom by blast
  qed
  then show ?thesis
    using \<open>\<exists>y>- r. a * y\<^sup>2 + b * y + c < 0\<close> beq by auto 
qed


lemma one_root_a_lt0_var:
  fixes a b c r y'::"real"
  assumes alt: "a < 0"
  assumes beq: "b = 2 * a * r"
  assumes root: " a * r^2 - 2*a*r*r + c = 0"
  shows "\<exists>y'>- r. \<forall>x\<in>{- r<..y'}. a * x\<^sup>2 + 2*a*r*x + c \<le> 0"
proof - 
  have h1: "\<exists>y'>- r. \<forall>x\<in>{- r<..y'}. a * x\<^sup>2 + 2 * a * r * x + c < 0 \<Longrightarrow>
     \<exists>y'>-r. \<forall>x\<in>{- r<..y'}. a * x\<^sup>2 + 2 * a *r * x + c \<le> 0"
    using less_eq_real_def by blast
  then show ?thesis
    using one_root_a_lt0[of a b r] assms by auto
qed

subsection "More Continuity Properties"
lemma continuity_lem_gt0_expanded_var: 
  fixes r:: "real"
  fixes a b c:: "real"
  fixes k::"real"
  assumes kgt: "k > r"
  shows "a*r^2 + b*r + c > 0 \<Longrightarrow>
    \<exists>x\<in>{r<..k}. a*x^2 + b*x + c \<ge> 0"
proof -
  assume a: "a*r^2 + b*r + c > 0  "
  have h: "\<exists>x\<in>{r<..k}. a*x^2 + b*x + c > 0  \<Longrightarrow> \<exists>x\<in>{r<..k}. a*x^2 + b*x + c \<ge> 0"
    using less_eq_real_def by blast 
  have "\<exists>x\<in>{r<..k}. a*x^2 + b*x + c > 0" using a continuity_lem_gt0_expanded[of r k a b c] assms by auto
  then show "\<exists>x\<in>{r<..k}. a*x^2 + b*x + c \<ge> 0"
    using h by auto
qed

lemma continuity_lem_lt0_expanded_var: 
  fixes r:: "real"
  fixes a b c:: "real"
  shows "a*r^2 + b*r + c < 0 \<Longrightarrow>
    \<exists>y'> r. \<forall>x\<in>{r<..y'}. a*x^2 + b*x + c \<le> 0"
proof - 
  assume "a*r^2 + b*r + c < 0 "
  then have " \<exists>y'> r. \<forall>x\<in>{r<..y'}. a*x^2 + b*x + c < 0"
    using continuity_lem_lt0_expanded by auto
  then show " \<exists>y'> r. \<forall>x\<in>{r<..y'}. a*x^2 + b*x + c \<le> 0"
    using less_eq_real_def by auto
qed

lemma nonzcoeffs:
  fixes a b c r::"real"
  shows "a\<noteq>0 \<or> b\<noteq>0 \<or> c\<noteq>0 \<Longrightarrow> \<exists>y'>r. \<forall>x\<in>{r<..y'}. a * x\<^sup>2 + b * x + c \<noteq> 0 "
proof - 
  assume "a\<noteq>0 \<or> b\<noteq>0 \<or> c\<noteq>0"
  then have fin: "finite {x. a*x^2 + b*x + c = 0}"
    by (metis pCons_eq_0_iff poly_roots_finite poly_roots_set_same) 
      (* then have fin2: "finite {x. a*x^2 + b*x + c = 0 \<and> x > r}"
    using finite_Collect_conjI by blast *)
  let ?s = "{x. a*x^2 + b*x + c = 0}"
  have imp: "(\<exists>q \<in> ?s. q > r) \<Longrightarrow> (\<exists>q \<in> ?s. (q > r \<and> (\<forall>x \<in> ?s. x > r \<longrightarrow> x \<ge> q)))"
  proof - 
    assume asm: "(\<exists>q \<in> ?s. q > r)"
    then have none: "{q. q \<in> ?s \<and> q > r} \<noteq> {}"
      by blast 
    have fin2: "finite {q. q \<in> ?s \<and> q > r}" using fin
      by simp
    have "\<exists>k. k = Min  {q. q \<in> ?s \<and> q > r}" using fin2 none
      by blast
    then obtain k where k_prop: "k =  Min  {q. q \<in> ?s \<and> q > r}" by auto
    then have kp1: "k \<in> ?s \<and> k > r" 
      using Min_in fin2 none
      by blast 
    then  have kp2: "\<forall>x \<in> ?s. x > r \<longrightarrow> x \<ge> k" 
      using Min_le fin2  using k_prop by blast 
    show "(\<exists>q \<in> ?s. (q > r \<and> (\<forall>x \<in> ?s. x > r \<longrightarrow> x \<ge> q)))" 
      using kp1 kp2 by blast
  qed
  have h2: "(\<exists>q \<in> ?s. q > r) \<Longrightarrow> \<exists>y'>r. \<forall>x\<in>{r<..y'}. a * x\<^sup>2 + b * x + c \<noteq> 0" 
  proof - 
    assume "(\<exists>q \<in> ?s. q > r)"
    then obtain q where q_prop: "q \<in> ?s \<and> (q > r \<and> (\<forall>x \<in> ?s. x > r \<longrightarrow> x \<ge> q))"
      using imp by blast 
    then have "\<exists>w. w > r \<and> w < q" using dense
      by blast
    then obtain w where w_prop: "w > r \<and> w < q" by auto
    then have "\<not>(\<exists>x\<in>{r<..w}. x \<in> ?s)"
      using w_prop q_prop by auto
    then have "\<forall>x\<in>{r<..w}. a * x\<^sup>2 + b * x + c \<noteq> 0"
      by blast
    then show "\<exists>y'>r. \<forall>x\<in>{r<..y'}. a * x\<^sup>2 + b * x + c \<noteq> 0"
      using w_prop by blast
  qed
  have h1: "\<not>(\<exists>q \<in> ?s. q > r) \<Longrightarrow> \<exists>y'>r. \<forall>x\<in>{r<..y'}. a * x\<^sup>2 + b * x + c \<noteq> 0"
  proof - 
    assume "\<not>(\<exists>q \<in> ?s. q > r)"
    then have "\<forall>x\<in>{r<..(r+1)}. a * x\<^sup>2 + b * x + c \<noteq> 0"
      using greaterThanAtMost_iff by blast
    then show ?thesis
      using less_add_same_cancel1 less_numeral_extra(1) by blast 
  qed
  then show "\<exists>y'>r. \<forall>x\<in>{r<..y'}. a * x\<^sup>2 + b * x + c \<noteq> 0"
    using h2 by blast
qed


(* Show if there are infinitely many values of x where a*x^2 + b*x + c is 0,
then the a*x^2 + b*x + c is the zero polynomial *)
lemma infzeros : 
  fixes y:: "real"
  assumes "\<forall>x::real < (y::real). a * x\<^sup>2 + b * x + c = 0"
  shows "a = 0 \<and> b=0 \<and> c=0"
proof - 
  let ?A = "{(x::real). x < y}"
  have "\<exists> (n::nat) f. ?A = f ` {i. i < n} \<and> inj_on f {i. i < n} \<Longrightarrow> False"
  proof clarsimp 
    fix n:: "nat" 
    fix f
    assume xlt: "{x. x < y} = f ` {i. i < n}"
    assume injh: "inj_on f {i. i < n}"
    have "?A \<noteq> {}"
      by (simp add: linordered_field_no_lb)
    then have ngtz: "n > 0" 
      using xlt injh using gr_implies_not_zero by auto 
    have cardisn: "card ?A = n" using xlt injh
      by (simp add: card_image) 
    have "\<forall>k::nat. ((y - (k::nat) - 1) \<in> ?A)" 
      by auto
    then have subs: "{k. \<exists>(x::nat). k = y - x - 1 \<and> 0 \<le> x \<and> x \<le> n} \<subseteq> ?A"
      by auto
    have seteq: "(\<lambda>x. y - real x - 1) ` {0..n} ={k. \<exists>(x::nat). k = y - x - 1 \<and> 0 \<le> x \<and> x \<le> n}"
      by auto
    have injf: "inj_on (\<lambda>x. y - real x - 1) {0..n}"
      unfolding inj_on_def by auto
    have "card {k. \<exists>(x::nat). k = y - x - 1 \<and> 0 \<le> x \<and> x \<le> n} = n + 1"
      using  injf seteq card_atMost inj_on_iff_eq_card[where A = "{0..n}", where f = "\<lambda>x. y - x - 1"] 
      by auto
    then have if_fin: "finite ?A \<Longrightarrow> card ?A \<ge> n + 1" 
      using subs card_mono
      by (metis (lifting) card_mono)
    then have if_inf: "infinite ?A \<Longrightarrow> card ?A = 0"
      by (meson card.infinite)
    then show "False" using if_fin if_inf cardisn ngtz by auto
  qed
  then have nfin: "\<not> finite {(x::real). x < y}"
    using finite_imp_nat_seg_image_inj_on by blast
  have "{(x::real). x < y} \<subseteq> {x. a*x^2 + b*x + c = 0}"
    using assms by auto
  then have nfin2: "\<not> finite {x. a*x^2 + b*x + c = 0}"
    using nfin finite_subset by blast 
  {
    fix x
    assume "a * x\<^sup>2 + b * x + c = 0"
    then have f1: "a * (x * x) + x * b + c = 0"
      by (simp add: Groups.mult_ac(2) power2_eq_square)
    have f2: "\<forall>r. c + (r + (c + - c)) = r + c"
      by simp
    have f3: "\<forall>r ra rb. (rb::real) * ra + ra * r = (rb + r) * ra"
      by (metis Groups.mult_ac(2) Rings.ring_distribs(2))
    have "\<forall>r. r + (c + - c) = r"
      by simp
    then have "c + x * (b + x * a) = 0"
      using f3 f2 f1 by (metis Groups.add_ac(3) Groups.mult_ac(1) Groups.mult_ac(2))
  }
  hence "{x. a*x^2 + b*x + c = 0} \<subseteq> {x. poly [:c, b, a:] x = 0}"
    by auto
  then have " \<not> finite {x. poly [:c, b, a:] x = 0}" 
    using nfin2 using finite_subset by blast 
  then have "[:c, b, a:] = 0" 
    using poly_roots_finite[where p = "[:c, b, a:]"]  by auto
  then show ?thesis
    by auto
qed



lemma have_inbetween_point_leq:
  fixes r::"real"
  assumes "(\<forall>((d::real), (e::real), (f::real))\<in>set leq. \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)"
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set leq. a * x\<^sup>2 + b * x + c \<le> 0))"
proof -
  have "(\<forall>(d, e, f)\<in>set leq. \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<Longrightarrow> 
    (\<exists>y'>r. (\<forall>(d, e, f)\<in>set leq. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0))"
    using leq_qe_inf_helper assms by auto
  then have "(\<exists>y'>r. (\<forall>(d, e, f)\<in>set leq. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0))"
    using assms
    by blast 
  then obtain y where y_prop: "y > r \<and>  (\<forall>(d, e, f)\<in>set leq. \<forall>x\<in>{r<..y}. d * x\<^sup>2 + e * x + f \<le> 0)"
    by auto
  have "\<exists>q. q >  r \<and>q < y" using y_prop dense by auto
  then obtain q where q_prop: "q > r \<and> q < y" by auto
  then have "(\<forall>(d, e, f)\<in>set leq. d*q^2 + e*q + f \<le> 0)"
    using y_prop by auto
  then show ?thesis
    by auto
qed


lemma have_inbetween_point_neq:
  fixes r::"real"
  assumes "(\<forall>((d::real), (e::real), (f::real))\<in>set neq. \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set neq. a * x\<^sup>2 + b * x + c \<noteq> 0))"
proof -
  have "(\<forall>(d, e, f)\<in>set neq. \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<Longrightarrow> 
    (\<exists>y'>r. (\<forall>(d, e, f)\<in>set neq. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
    using neq_qe_inf_helper assms by auto
  then have "(\<exists>y'>r. (\<forall>(d, e, f)\<in>set neq. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
    using assms
    by blast 
  then obtain y where y_prop: "y > r \<and>  (\<forall>(d, e, f)\<in>set neq. \<forall>x\<in>{r<..y}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
    by auto
  have "\<exists>q. q >  r \<and>q < y" using y_prop dense by auto
  then obtain q where q_prop: "q > r \<and> q < y" by auto
  then have "(\<forall>(d, e, f)\<in>set neq. d*q^2 + e*q + f \<noteq> 0)"
    using y_prop by auto
  then show ?thesis
    by auto
qed

subsection "Setting up and Helper Lemmas"
subsubsection "The les\\_qe lemma"
lemma les_qe_forward : 
  shows "(((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0))))) \<Longrightarrow> ((\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)))"
proof -
  assume big_asm: "(((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0)))))"
  then have big_or: "(\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or> 
               (\<exists>(a', b', c')\<in>set les.
               a' = 0 \<and>
               b' \<noteq> 0 \<and> (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0)) 
        \<or>
        (\<exists>(a', b', c')\<in>set les.
               a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
               (\<forall>(d, e, f)\<in>set les.
                   \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                      \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)) 
      \<or>
      (\<exists>(a', b', c')\<in>set les.  a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
                (\<forall>(d, e, f)\<in>set les.
                    \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                       \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                          d * x\<^sup>2 + e * x + f < 0)) " 
    by auto
  have h1_helper: "(\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  proof - 
    show "(\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))" 
    proof (induct les)
      case Nil
      then show ?case
        by auto
    next
      case (Cons q les) 
      have ind: " \<forall>a\<in>set (q # les). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0"
        using Cons.prems
        by auto
      then have "case q of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0 "
        by simp      
      then obtain y2 where y2_prop: "case q of (a, ba, c) \<Rightarrow>  (\<forall>y<y2. a * y\<^sup>2 + ba * y + c < 0)"
        by auto
      have "\<forall>a\<in>set les. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0"
        using ind by simp
      then have " \<exists>y. \<forall>x<y. \<forall>a\<in>set les. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c < 0"
        using Cons.hyps by blast 
      then obtain y1 where y1_prop: "\<forall>x<y1. \<forall>a\<in>set les. case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c < 0"
        by blast
      let ?y = "min y1 y2"
      have "\<forall>x < ?y.  (\<forall>a\<in>set (q #les). case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c < 0)"
        using y1_prop y2_prop 
        by fastforce 
      then show ?case
        by blast 
    qed
  qed
  then have h1: "(\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<Longrightarrow>(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
    by (smt (z3) infzeros less_eq_real_def not_numeral_le_zero)
      (* apply (auto)
    by (metis (lifting) infzeros zero_neq_numeral) *)
  have h2: " (\<exists>(a', b', c')\<in>set les.
               a' = 0 \<and>
               b' \<noteq> 0 \<and> (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0))
    \<Longrightarrow> (\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  proof -
    assume asm: "(\<exists>(a', b', c')\<in>set les. a' = 0 \<and> b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0))"
    then obtain a' b' c' where abc_prop: "(a', b', c') \<in>set les \<and> a' = 0 \<and> b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0)"
      by auto
    then show "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
      using have_inbetween_point_les by auto
  qed
  have h3: " (\<exists>(a', b', c')\<in>set les.
               a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
               (\<forall>(d, e, f)\<in>set les.
                   \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                      \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)) \<Longrightarrow> ((\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)))"
  proof - 
    assume asm: "\<exists>(a', b', c')\<in>set les.  a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
                \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                   \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                      d * x\<^sup>2 + e * x + f < 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set les \<and> a' \<noteq> 0 \<and> 4 * a' * c' \<le> b'\<^sup>2 \<and>
       (\<forall>(d, e, f)\<in>set les.
           \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
              \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)"
      by auto
    then show "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
      using have_inbetween_point_les by auto
  qed
  have h4: "(\<exists>(a', b', c')\<in>set les.  a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
                (\<forall>(d, e, f)\<in>set les.
                    \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                       \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                          d * x\<^sup>2 + e * x + f < 0)) \<Longrightarrow> (\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  proof - 
    assume asm: "(\<exists>(a', b', c')\<in>set les.  a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0)) "
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set les \<and> a' \<noteq> 0 \<and> 4 * a' * c' \<le> b'\<^sup>2 \<and>
     (\<forall>(d, e, f)\<in>set les.
         \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
            \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)"
      by auto
    then have "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
      using have_inbetween_point_les by auto
    then show ?thesis using asm by auto
  qed 
  show ?thesis using big_or h1 h2 h3 h4
    by blast 
qed

(*sample points, some starter proofs below in comments *)
lemma les_qe_backward : 
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<Longrightarrow>
    ((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0))))"

proof - 
  assume havex: "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  then obtain x where x_prop: "\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0" by auto
  have h: "(\<not> (\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and> \<not> (\<exists>(a', b', c')\<in>set les.
           a' = 0 \<and>
           b' \<noteq> 0 \<and>
           (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0)) \<and>
        \<not> (\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                  \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)) \<and>
        \<not> (\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0))) \<Longrightarrow> False"
  proof -
    assume big: "(\<not> (\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and> \<not> (\<exists>(a', b', c')\<in>set les.
           a' = 0 \<and>
           b' \<noteq> 0 \<and>
           (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0)) \<and>
        \<not> (\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                  \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)) \<and>
        \<not> (\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)))"
    have notneginf: "\<not> (\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0)" using big by auto
    have notlinroot: "\<not> (\<exists>(a', b', c')\<in>set les.
           a' = 0 \<and>
           b' \<noteq> 0 \<and>
           (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0))" 
      using big by auto
    have notquadroot1: " \<not> (\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                  \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0))"
      using big by auto
    have notquadroot2:" \<not> (\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0))"
      using big by auto
    have nok: "\<not> (\<exists>k. \<exists>(a, b, c)\<in>set les. a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0))"
    proof - 
      have "(\<exists>k. \<exists>(a, b, c)\<in>set les. a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0)) \<Longrightarrow> False"
      proof - 
        assume "(\<exists>k. \<exists>(a, b, c)\<in>set les. a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0))"
        then obtain k a b c where k_prop: "(a, b, c) \<in> set les \<and>  a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0)"
          by auto
        have azer:  "a = 0 \<Longrightarrow> False"
        proof - 
          assume azer: "a = 0"
          then have "b = 0 \<Longrightarrow> c = 0" using k_prop by auto
          then have bnonz: "b\<noteq> 0"
            using azer x_prop k_prop 
            by auto 
          then have "k = -c/b" using k_prop azer
            by (metis (no_types, hide_lams) add.commute add.left_neutral add_uminus_conv_diff diff_le_0_iff_le divide_non_zero less_eq_real_def mult_zero_left neg_less_iff_less order_less_irrefl real_add_less_0_iff)
          then have " (\<exists>(a', b', c')\<in>set les.
           a' = 0 \<and> b' \<noteq> 0 \<and> (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0))"
            using k_prop azer bnonz by auto
          then show "False" using notlinroot
            by auto
        qed
        have anonz: "a \<noteq> 0 \<Longrightarrow> False"
        proof - 
          assume anonz: "a \<noteq> 0 "
          let ?r1 = "(- b - sqrt (b^2 - 4 * a * c)) / (2 * a)"
          let ?r2 = "(- b + sqrt (b^2 - 4 * a * c)) / (2 * a)"
          have discr: "4 * a * c \<le> b^2" using anonz k_prop discriminant_negative[of a b c] 
            unfolding discrim_def 
            by fastforce 
          then have "k = ?r1 \<or> k = ?r2" using k_prop discriminant_nonneg[of a b c] unfolding discrim_def
            using anonz
            by auto 
          then have "(\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                  \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)) \<or>
           (\<exists>(a', b', c')\<in>set les.
           a' \<noteq> 0 \<and>
           4 * a' * c' \<le> b'\<^sup>2 \<and>
           (\<forall>(d, e, f)\<in>set les.
               \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0))"
            using discr anonz notquadroot1 notquadroot2 k_prop 
            by auto
          then show "False" using  notquadroot1 notquadroot2
            by auto
        qed
        show "False"
          using azer anonz  by auto
      qed
      then show ?thesis by auto
    qed
    have finset: "finite (set les)"
      by blast
    have h1: "(\<exists>(a, b, c)\<in>set les. a = 0 \<and> b = 0 \<and> c = 0)  \<Longrightarrow> False"
      using x_prop by fastforce
    then have h2: "\<not>(\<exists>(a, b, c)\<in>set les. a = 0 \<and> b = 0 \<and> c = 0) \<Longrightarrow> False"
    proof - 
      assume nozer: "\<not>(\<exists>(a, b, c)\<in>set les. a = 0 \<and> b = 0 \<and> c = 0)"
      then have same_set: "root_set (set les) = set (sorted_root_list_set (set les))"
        using root_set_finite finset set_sorted_list_of_set
        by (simp add: nozer root_set_finite sorted_root_list_set_def)
      have xnotin: "x \<notin> root_set (set les)"
        unfolding root_set_def using x_prop by auto
      let ?srl = "sorted_root_list_set (set les)"
      have notinlist: "\<not> List.member ?srl x"
        using xnotin same_set
        by (simp add: in_set_member)
      then have notmem: "\<forall>n < (length ?srl). x \<noteq> nth_default 0 ?srl n"
        using nth_mem same_set xnotin nth_default_def
        by metis  
      show ?thesis 
      proof (induct ?srl)
        case Nil
        then have "(\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0)"
        proof clarsimp 
          fix a b c
          assume noroots: "[] = sorted_root_list_set (set les)"
          assume inset: "(a, b, c) \<in> set les"
          have "{} = root_set (set les)" 
            using noroots same_set 
            by auto 
          then have nozero: "\<not>(\<exists>x. a*x^2  + b*x + c = 0)"
            using inset unfolding root_set_def by auto
          have "\<forall>y<x. a * y\<^sup>2 + b * y + c < 0" 
          proof clarsimp 
            fix y
            assume "y < x"
            then have "sign_num (a*x^2 + b*x + c) = sign_num (a*y^2 + b*y + c)"
              using nozero  by (metis changes_sign_var) 
            then show "a * y\<^sup>2 + b * y + c < 0"
              unfolding sign_num_def using x_prop inset 
              by (smt split_conv) 
          qed
          then show "\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0"
            by auto
        qed
        then show ?case using notneginf by auto
      next
        case (Cons w xa) 
          (* Need to argue that x isn't greater than the largest element of ?srl *)
          (* that if srl has length \<ge> 2, x isn't in between any of the roots of ?srl*)
          (* and that x isn't less than the lowest root in ?srl *)
        then have lengthsrl: "length ?srl > 0" by auto
        have neginf: "x < nth_default 0 ?srl 0 \<Longrightarrow> False"
        proof -
          assume xlt: "x < nth_default 0 ?srl 0"
          have all: "(\<forall>(a, b, c)\<in>set les. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0)"
          proof clarsimp 
            fix a b c y
            assume inset: "(a, b, c) \<in> set les"
            assume "y < x"
            have xl: "a*x^2 + b*x + c < 0" using x_prop inset by auto
            have "\<not>(\<exists>q. q < nth_default 0 ?srl 0  \<and> a*q^2 + b*q + c = 0)"
            proof - 
              have "(\<exists>q. q < nth_default 0 ?srl 0  \<and> a*q^2 + b*q + c = 0) \<Longrightarrow> False"
              proof - assume "\<exists>q. q < nth_default 0 ?srl 0  \<and> a*q^2 + b*q + c = 0"
                then obtain q where q_prop: "q < nth_default 0 ?srl 0 \<and>a*q^2 + b*q + c = 0" by auto
                then have " q \<in> root_set (set les)" unfolding root_set_def using inset by auto
                then have "List.member ?srl q" using same_set
                  by (simp add: in_set_member)
                then have "q \<ge> nth_default 0 ?srl 0"
                  using sorted_sorted_list_of_set[where A = "root_set (set les)"]
                  unfolding sorted_root_list_set_def
                  by (metis \<open>q \<in> root_set (set les)\<close> in_set_conv_nth le_less_linear lengthsrl not_less0 nth_default_nth same_set sorted_nth_mono sorted_root_list_set_def)
                then show "False" using q_prop by auto
              qed
              then show ?thesis by auto
            qed
            then have "\<not>(\<exists>q. q < x \<and> a*q^2 + b*q + c = 0)" using xlt by auto
            then show " a * y\<^sup>2 + b * y + c < 0" 
              using xl changes_sign_var[where a = "a", where b = "b", where c = "c", where x = "y", where y = "x"]
              unfolding sign_num_def using \<open>y < x\<close> less_eq_real_def zero_neq_numeral 
              by fastforce
          qed
          have "(\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0)"
          proof clarsimp 
            fix a b c
            assume "(a, b, c)\<in>set les"
            then show "\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0" 
              using all by blast 
          qed
          then show "False" using notneginf by auto
        qed
        have "x > nth_default 0 ?srl (length ?srl - 1) \<Longrightarrow> (\<exists>k. \<exists>(a, b, c)\<in>set les. a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0))"
        proof - 
          assume xgt: "x > nth_default 0 ?srl (length ?srl - 1)"
          let ?lg = "nth_default 0 ?srl (length ?srl - 1)"
          have "List.member ?srl ?lg"
            by (metis diff_less in_set_member lengthsrl nth_default_def nth_mem zero_less_one)
          then have "?lg \<in> root_set (set les) "
            using same_set in_set_member[of ?lg ?srl]  by auto
          then have exabc: "\<exists>(a, b, c)\<in>set les. a*?lg^2 + b*?lg + c = 0"
            unfolding root_set_def by auto
          have "(\<forall>(d, e, f)\<in>set les. \<forall>q\<in>{?lg<..x}. d * q^2 + e * q + f < 0)"
          proof clarsimp 
            fix d e f q 
            assume inset: "(d, e, f) \<in> set les"
            assume qgt: "(nth_default 0) (sorted_root_list_set (set les)) (length (sorted_root_list_set (set les)) - Suc 0) < q"
            assume qlt: "q \<le> x"
            have nor: "\<not>(\<exists>r. d * r^2 + e * r + f = 0 \<and> r > ?lg)"
            proof - 
              have "(\<exists>r. d * r^2 + e * r + f = 0 \<and> r > ?lg) \<Longrightarrow> False "
              proof - 
                assume "\<exists>r. d * r^2 + e * r + f = 0 \<and> r > ?lg"
                then obtain r where r_prop: "d*r^2 + e*r + f = 0 \<and> r > ?lg" by auto
                then have "r \<in> root_set (set les)" using inset unfolding root_set_def by auto
                then have "List.member ?srl r"
                  using same_set in_set_member
                  by (simp add: in_set_member) 
                then have " r \<le> ?lg" using sorted_sorted_list_of_set nth_default_def
                  by (metis One_nat_def Suc_pred \<open>r \<in> root_set (set les)\<close> in_set_conv_nth lengthsrl lessI less_Suc_eq_le same_set sorted_nth_mono sorted_root_list_set_def)
                then show "False" using r_prop by auto
              qed
              then show ?thesis by auto
            qed
            then have xltz_helper: "\<not>(\<exists>r. r \<ge> q \<and> d * r^2 + e * r + f = 0)"
              using qgt by auto
            then have xltz: "d*x^2 + e*x + f < 0" using inset x_prop by auto
            show "d * q\<^sup>2 + e * q + f < 0"
              using qlt qgt nor changes_sign_var[of d _ e f _] xltz xltz_helper unfolding sign_num_def
              apply (auto) 
              by smt
          qed
          then have " (\<forall>(d, e, f)\<in>set les. \<exists>y'>?lg. \<forall>x\<in>{?lg<..y'}. d * x\<^sup>2 + e * x + f < 0)"
            using xgt by auto
          then have "(\<exists>(a, b, c)\<in>set les. a*?lg^2 + b*?lg + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>?lg. \<forall>x\<in>{?lg<..y'}. d * x\<^sup>2 + e * x + f < 0))"
            using exabc by auto
          then show "(\<exists>k. \<exists>(a, b, c)\<in>set les. a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0))"
            by auto
        qed
        then have posinf: "x > nth_default 0 ?srl (length ?srl - 1) \<Longrightarrow> False" 
          using nok by auto
        have "(\<exists>n. (n+1) < (length ?srl) \<and> x > (nth_default 0 ?srl) n \<and> x < (nth_default 0 ?srl (n + 1))) \<Longrightarrow> (\<exists>k. \<exists>(a, b, c)\<in>set les. a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0))"
        proof - 
          assume "\<exists>n. (n+1) < (length ?srl) \<and> x > nth_default 0 ?srl n \<and> x < nth_default 0 ?srl (n + 1)"
          then obtain n where n_prop: "(n+1) < (length ?srl) \<and> x > nth_default 0 ?srl n \<and> x < nth_default 0 ?srl (n + 1)" by auto
          let ?elt = "nth_default 0 ?srl n"
          let ?elt2 = "nth_default 0 ?srl (n + 1)"
          have "List.member ?srl ?elt"
            using n_prop nth_default_def
            by (metis add_lessD1 in_set_member nth_mem) 
          then have "?elt \<in> root_set (set les) "
            using same_set in_set_member[of ?elt ?srl]  by auto
          then have exabc: "\<exists>(a, b, c)\<in>set les. a*?elt^2 + b*?elt + c = 0"
            unfolding root_set_def by auto
          then obtain a b c where "(a, b, c)\<in>set les \<and> a*?elt^2 + b*?elt + c = 0"
            by auto
          have xltel2: "x < ?elt2" using n_prop by auto
          have xgtel: "x > ?elt " using n_prop by auto
          have "(\<forall>(d, e, f)\<in>set les. \<forall>q\<in>{?elt<..x}. d * q^2 + e * q + f < 0)"
          proof clarsimp 
            fix d e f q 
            assume inset: "(d, e, f) \<in> set les"
            assume qgt: "nth_default 0 (sorted_root_list_set (set les)) n < q"
            assume qlt: "q \<le> x"

            have nor: "\<not>(\<exists>r. d * r^2 + e * r + f = 0 \<and> r > ?elt \<and>r < ?elt2)"
            proof - 
              have "(\<exists>r. d * r^2 + e * r + f = 0 \<and> r > ?elt \<and> r < ?elt2) \<Longrightarrow> False "
              proof - 
                assume "\<exists>r. d * r^2 + e * r + f = 0 \<and> r > ?elt  \<and> r < ?elt2"
                then obtain r where r_prop: "d*r^2 + e*r + f = 0 \<and> r > ?elt  \<and> r < ?elt2" by auto
                then have "r \<in> root_set (set les)" using inset unfolding root_set_def by auto
                then have "List.member ?srl r"
                  using same_set in_set_member
                  by (simp add: in_set_member) 
                then have "\<exists>i < (length ?srl). r = nth_default 0 ?srl i"
                  by (metis \<open>r \<in> root_set (set les)\<close> in_set_conv_nth same_set nth_default_def)
                then obtain i where i_prop: "i < (length ?srl) \<and> r = nth_default 0 ?srl i"
                  by auto
                have "r > ?elt" using r_prop by auto
                then  have igt: " i > n" using i_prop sorted_sorted_list_of_set
                  by (smt add_lessD1 leI n_prop nth_default_def sorted_nth_mono sorted_root_list_set_def)
                have "r < ?elt2" using r_prop by auto
                then have ilt: " i < n + 1" using i_prop sorted_sorted_list_of_set
                  by (smt leI n_prop nth_default_def sorted_nth_mono sorted_root_list_set_def) 
                then show "False"  using igt ilt
                  by auto
              qed
              then show ?thesis by auto
            qed
            then have nor: "\<not>(\<exists>r. d * r^2 + e * r + f = 0 \<and> r > ?elt \<and>r \<le> x)"
              using xltel2 xgtel by auto
            then have xltz: "d*x^2 + e*x + f < 0" using inset x_prop by auto
            show "d * q\<^sup>2 + e * q + f < 0"
              using qlt qgt nor changes_sign_var[of d _ e f _] xltz unfolding sign_num_def
              by smt 
          qed
          then have " (\<forall>(d, e, f)\<in>set les. \<exists>y'>?elt. \<forall>x\<in>{?elt<..y'}. d * x\<^sup>2 + e * x + f < 0)"
            using xgtel xltel2 by auto
          then have "(\<exists>(a, b, c)\<in>set les. a*?elt^2 + b*?elt + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>?elt. \<forall>x\<in>{?elt<..y'}. d * x\<^sup>2 + e * x + f < 0))"
            using exabc by auto
          then show "(\<exists>k. \<exists>(a, b, c)\<in>set les. a*k^2 + b*k + c = 0 \<and>
                (\<forall>(d, e, f)\<in>set les. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0))"
            by auto
        qed
        then have inbetw: "(\<exists>n. (n+1) < (length ?srl) \<and> x > nth_default 0 ?srl n \<and> x < nth_default 0 ?srl (n + 1)) \<Longrightarrow> False"
          using nok by auto
        have lenzer: "length xa = 0 \<Longrightarrow> False" 
        proof - 
          assume "length xa = 0"
          have xis: "x > w \<or> x < w"
            using notmem Cons.hyps
            by (smt list.set_intros(1) same_set xnotin) 
          have xgt: "x > w \<Longrightarrow> False"
          proof - 
            assume xgt: "x > w"
            show "False" using posinf Cons.hyps
              by (metis One_nat_def Suc_eq_plus1 \<open>length xa = 0\<close> cancel_comm_monoid_add_class.diff_cancel list.size(4) nth_default_Cons_0 xgt)
          qed
          have xlt: "x < w \<Longrightarrow> False"
          proof - 
            assume xlt: "x < w"
            show "False" using neginf Cons.hyps
              by (metis nth_default_Cons_0 xlt) 
          qed
          show "False" using xis xgt xlt by auto
        qed
        have lengt: "length xa > 0 \<Longrightarrow> False"
        proof - 
          assume "length xa > 0"
          have "x \<ge> nth_default 0 ?srl 0" using neginf
            by fastforce
          then have xgtf: "x > nth_default 0 ?srl 0" using notmem
            using Cons.hyps(2) by fastforce
          have "x \<le> nth_default 0 ?srl (length ?srl - 1)" using posinf by fastforce
          then have "(\<exists>n. (n+1) < (length ?srl) \<and> x \<ge> nth_default 0 ?srl n \<and> x \<le> nth_default 0 ?srl (n + 1))"
            using lengthsrl xgtf notmem sorted_list_prop[where l = ?srl, where x = "x"]
            by (metis add_lessD1 diff_less nth_default_nth sorted_root_list_set_def sorted_sorted_list_of_set zero_less_one)
          then obtain n where n_prop: "(n+1) < (length ?srl) \<and> x \<ge> nth_default 0 ?srl n \<and> x \<le> nth_default 0 ?srl (n + 1)" by auto
          then have "x > nth_default 0 ?srl n \<and> x < nth_default 0 ?srl (n+1)"
            using notmem
            by (metis Suc_eq_plus1 Suc_lessD less_eq_real_def)
          then have "(\<exists>n. (n+1) < (length ?srl) \<and> x > nth_default 0 ?srl n \<and> x < nth_default 0 ?srl (n + 1))"
            using n_prop
            by blast  
          then show "False" using inbetw by auto
        qed
        then show ?case using lenzer lengt by auto
      qed 
    qed
    show "False"
      using h1 h2 by auto
  qed
  then have equiv_false: "\<not>((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or> 
               (\<exists>(a', b', c')\<in>set les.
               a' = 0 \<and>
               b' \<noteq> 0 \<and> (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0)) 
        \<or>
        (\<exists>(a', b', c')\<in>set les.
               a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
               (\<forall>(d, e, f)\<in>set les.
                   \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                      \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)) 
      \<or>
      (\<exists>(a', b', c')\<in>set les.  a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
                (\<forall>(d, e, f)\<in>set les.
                    \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                       \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                          d * x\<^sup>2 + e * x + f < 0))) \<Longrightarrow> False"
    by linarith
  have "\<not>((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0)))) \<Longrightarrow> False"
  proof - 
    assume "\<not>((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0))))"
    then have "\<not>((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or> 
               (\<exists>(a', b', c')\<in>set les.
               a' = 0 \<and>
               b' \<noteq> 0 \<and> (\<forall>(d, e, f)\<in>set les. \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0)) 
        \<or>
        (\<exists>(a', b', c')\<in>set les.
               a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
               (\<forall>(d, e, f)\<in>set les.
                   \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                      \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}. d * x\<^sup>2 + e * x + f < 0)) 
      \<or>
      (\<exists>(a', b', c')\<in>set les.  a' \<noteq> 0 \<and>
               4 * a' * c' \<le> b'\<^sup>2 \<and>
                (\<forall>(d, e, f)\<in>set les.
                    \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                       \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                          d * x\<^sup>2 + e * x + f < 0)))"
      by auto
    then show ?thesis
      using equiv_false by auto
  qed
  then show ?thesis
    by blast 
qed

lemma les_qe : 
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) =
    ((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0))))"
proof -
  have first: "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<longrightarrow>
    ((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0))))"
    using les_qe_backward by auto
  have second: "((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0)))) \<longrightarrow> (\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) "
    using les_qe_forward by auto
  have "(\<exists>x. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<longleftrightarrow>
  ((\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or>
     (\<exists>(a', b', c')\<in>set les.
         a' = 0 \<and>
         b' \<noteq> 0 \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- (c' / b'). \<forall>x\<in>{- (c' / b')<..y'}. d * x\<^sup>2 + e * x + f < 0) \<or>
         a' \<noteq> 0 \<and>
         4 * a' * c' \<le> b'\<^sup>2 \<and>
         ((\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a').
                 \<forall>x\<in>{(sqrt (b'\<^sup>2 - 4 * a' * c') - b') / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<or>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' - sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0))))"
    using first second
    by meson 
  then show ?thesis
    by blast
qed


subsubsection "equiv\\_lemma"
lemma equiv_lemma: 
  assumes big_asm: "(\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)) \<or>
  (\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
          
      (\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)) \<or>
     ((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  shows "((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))" 
proof - 
  let ?t = " ((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  have h1: "(\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)) \<Longrightarrow> ?t"
    by auto
  have h2: "(\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<Longrightarrow> ?t" 
    by auto
  have h3: "(\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)) \<Longrightarrow> ?t" 
    by auto
  show ?thesis
    using big_asm h1 h2 h3
    by presburger 
qed

subsubsection "The eq\\_qe lemma"
lemma eq_qe_forwards: 
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))  \<Longrightarrow>
    ((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
proof - 
  let ?big_or = "(\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)) \<or>
  (\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
          
      (\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)) \<or>
     ((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  assume asm: "(\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) " 
  then obtain x where x_prop: "(\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)" by auto
  have "\<not> (\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)) \<and>
  \<not> (\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<and>
          \<not> (\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)) \<and>
     \<not> ((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<Longrightarrow> False" 
  proof - 
    assume big_conj: "\<not> (\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)) \<and>
  \<not> (\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<and>
          \<not> (\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)) \<and>
     \<not> ((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
    have not_lin: "\<not>(\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0))"
      using big_conj by auto
    have not_quad1: "\<not>(\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)))"
      using big_conj by auto
    have not_quad2: "\<not>(\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))"
      using big_conj by auto
    have not_zer: "\<not>((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
      using big_conj by auto
    then have not_zer1: "\<not>(\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<or>
     \<not> (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)" by auto
    have "(\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)" using asm 
      by auto 
    then have "\<not>(\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0)" using not_zer1 by auto
    then have "\<exists> (d, e, f)\<in>set eq. d \<noteq> 0 \<or> e \<noteq> 0 \<or> f \<noteq> 0 "
      by auto
    then obtain d e f where def_prop: "(d, e, f) \<in> set eq \<and> (d \<noteq> 0 \<or> e \<noteq> 0 \<or> f \<noteq> 0)" by auto
    then have eval_at_x: "d*x^2 + e*x + f = 0" using x_prop by auto
    have dnonz: "d \<noteq> 0 \<Longrightarrow> False"
    proof - 
      assume dneq: "d \<noteq> 0"
      then have discr: "-(e^2) + 4 *d *f \<le> 0" using  discriminant_negative[of d e f x] eval_at_x unfolding discrim_def
        by linarith
      let ?r1 = "(- e + - 1 * sqrt (e^2 - 4 *d *f)) / (2 * d)"
      let ?r2 = "(- e + 1 * sqrt (e^2 - 4 *d *f)) / (2 * d)"
      have xis: "x = ?r1 \<or> x = ?r2"
        using dneq discr discriminant_nonneg[of d e f x] eval_at_x unfolding discrim_def
        by auto
      have xr1: "x = ?r1 \<Longrightarrow> False"
        using not_quad2 x_prop discr def_prop dneq by auto
      have xr2: "x = ?r2 \<Longrightarrow> False"
        using not_quad1 x_prop discr def_prop dneq by auto
      show "False" using xr1 xr2 xis by auto
    qed
    then have dz: "d = 0" by auto
    have enonz: "e \<noteq> 0 \<Longrightarrow> False" 
    proof - 
      assume enonz: "e\<noteq> 0"
      then have "x = -f/e" using dz eval_at_x
        by (metis add.commute minus_add_cancel mult.commute mult_zero_class.mult_zero_left nonzero_eq_divide_eq) 
      then show "False"
        using not_lin x_prop enonz dz def_prop by auto
    qed
    then have ez: "e = 0" by auto
    have fnonz: "f \<noteq> 0 \<Longrightarrow> False" using ez dz eval_at_x by auto
    show "False"
      using def_prop dnonz enonz fnonz by auto
  qed
  then have h: "\<not>(?big_or) \<Longrightarrow> False"
    by auto
  then show ?thesis using equiv_lemma
    by presburger
qed

lemma eq_qe_backwards: "((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<Longrightarrow> 
    (\<exists>x. ((\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)))
    "
proof - 
  assume "((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  then have bigor: "(\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)) \<or>
  (\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
          
      (\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)) \<or>
     ((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
    by auto
  have h1: "(\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)) \<Longrightarrow>
    (\<exists>(x::real). (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))" 
  proof - 
    assume "(\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0))"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set eq \<and>
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)" by auto
    let ?x = "(-c' /b')::real"
    have "(\<forall>(d, e, f)\<in>set eq. d * ?x\<^sup>2 + e * ?x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * ?x^2 + e * ?x + f < 0)" using abc_prop by auto
    then  show ?thesis using abc_prop by blast 
  qed
  have h2: " (\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<Longrightarrow> (\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  proof - 
    assume "(\<exists>(a', b', c')\<in>set eq.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)))"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set eq \<and> a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))" by auto
    let ?x = "((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')::real)"
    have anonz: "a' \<noteq> 0" using abc_prop by auto
    then have "\<exists>(q::real). q = ?x" by auto
    then obtain q where q_prop: "q = ?x" by auto
    have "(\<forall>(d, e, f)\<in>set eq. d * (?x)\<^sup>2 + e * (?x) + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set les. d * (?x)\<^sup>2 + e * (?x) + f < 0)"
      using abc_prop by auto
    then have "(\<forall>(d, e, f)\<in>set eq. d * q\<^sup>2 + e * q + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set les. d * q\<^sup>2 + e * q + f < 0)" using q_prop by auto
    then show ?thesis by auto
  qed
  have h3: "(\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)) \<Longrightarrow> (\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))" 
  proof - 
    assume "(\<exists>(a', b', c')\<in>set eq. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))"
    then obtain a' b' c' where abc_prop: "a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (a', b', c')\<in>set eq \<and> (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0)" by auto
    let ?x = "(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')"
    have anonz: "a' \<noteq> 0" using abc_prop by auto
    then have "\<exists>(q::real). q = ?x" by auto
    then obtain q where q_prop: "q = ?x" by auto
    have "(\<forall>(d, e, f)\<in>set eq. d * (?x)\<^sup>2 + e * (?x) + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set les. d * (?x)\<^sup>2 + e * (?x) + f < 0)"
      using abc_prop by auto
    then have "(\<forall>(d, e, f)\<in>set eq. d * q\<^sup>2 + e * q + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set les. d * q\<^sup>2 + e * q + f < 0)" using q_prop by auto
    then show ?thesis by auto
  qed
  have h4: "((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<Longrightarrow> (\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
  proof - 
    assume asm: "((\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
    then have allzer: "(\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0)" by auto
    have "(\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)" using asm by auto
    then obtain x where x_prop: " \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0" by auto
    then have "\<forall>(d, e, f)\<in>set eq. d*x^2 + e*x + f = 0"
      using allzer by auto
    then show ?thesis using x_prop by auto
  qed
  show ?thesis
    using bigor h1 h2 h3 h4
    by blast 
qed


lemma eq_qe : "(\<exists>x. ((\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))) =
    ((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
proof - 
  have h1: "(\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<longrightarrow>
    ((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
    using eq_qe_forwards by auto
  have h2: "((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<longrightarrow> (\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
    using eq_qe_backwards by auto
  have h3: "(\<exists>x. (\<forall>(a, b, c)\<in>set eq. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0)) \<longleftrightarrow>
    ((\<exists>(a', b', c')\<in>set eq.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0))) \<or>
     (\<forall>(d, e, f)\<in>set eq. d = 0 \<and> e = 0 \<and> f = 0) \<and>
     (\<exists>x. \<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
    using h1 h2
    by smt 
  then  show ?thesis
    by (auto) 
qed

subsubsection "The qe\\_forwards lemma"
lemma qe_forwards_helper_gen:
  fixes r:: "real"
  assumes f8: "\<not>(\<exists>((a'::real), (b'::real), (c'::real))\<in>set c. 
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         ((\<forall>(d, e, f)\<in>set a. d * r\<^sup>2 + e * r + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * r^2 + e * r + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * r^2 + e * r + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * r^2 + e * r + f \<noteq> 0)))"
  assumes alleqset: "\<forall>x. (\<forall>(d, e, f)\<in>set a. d * x^2 + e * x + f = 0)"
  assumes f5: "\<not>(\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f6: "\<not> (\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  assumes f7: "\<not> (\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f10: "\<not>(\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f11: "\<not>(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  assumes f12: "\<not>(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  shows "\<not>(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
proof - 
  have "(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)) \<Longrightarrow> False"
  proof - 
    assume "(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set c \<and>
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
      by auto
    have h1: "(\<forall>(d, e, f)\<in>set a. d * r^2 + e * r + f = 0)" 
      using alleqset
      by blast
    have c_prop: "(\<forall>(d, e, f)\<in>set c.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)" 
      using abc_prop by auto 
    have h2: "(\<forall>(d, e, f)\<in>set c. d *r^2 + e * r + f \<le> 0)" 
    proof - 
      have c1: "\<exists> (d, e, f) \<in> set c.  d * (r)\<^sup>2 + e * (r) + f > 0 \<Longrightarrow> False"
      proof - 
        assume "\<exists> (d, e, f) \<in> set c.  d * (r)\<^sup>2 + e * (r) + f > 0"
        then obtain d e f where def_prop: "(d, e, f) \<in> set c \<and> d * (r)\<^sup>2 + e * r + f > 0"
          by auto
        have "\<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0"
          using def_prop c_prop   by auto
        then obtain y' where y_prop: " y' >r \<and> (\<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)" by auto
        have "\<exists>x\<in>{r<..y'}. d*x^2 + e*x + f > 0"
          using def_prop continuity_lem_gt0_expanded[of "r" y' d e f]
          using y_prop by linarith 
        then show "False" using  y_prop
          by auto  
      qed
      then show ?thesis
        by fastforce 
    qed
    have b_prop: "(\<forall>(d, e, f)\<in>set b.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0)" 
      using abc_prop by auto
    have h3: "(\<forall>(d, e, f)\<in>set b. d * r\<^sup>2 + e * r + f < 0)" 
    proof - 
      have c1: "\<exists> (d, e, f) \<in> set b.  d * r\<^sup>2 + e * r + f > 0 \<Longrightarrow> False"
      proof - 
        assume "\<exists> (d, e, f) \<in> set b.  d * r\<^sup>2 + e * r + f > 0"
        then obtain d e f where def_prop: "(d, e, f) \<in> set b \<and> d * r\<^sup>2 + e * r + f > 0"
          by auto
        then have "\<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0"
          using b_prop by auto
        then obtain y' where y_prop: " y' >r \<and> (\<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0)" by auto
        then have "\<exists>k. k > r \<and> k < y' \<and> d * k^2 + e * k + f < 0" using dense
          by (meson dense greaterThanAtMost_iff less_eq_real_def) 
        then obtain k where k_prop: "k > r \<and> k < y' \<and> d * k^2 + e * k + f < 0" 
          by auto
        then have "\<not>(\<exists>x>r. x < y' \<and> d * x\<^sup>2 + e * x + f = 0)"
          using y_prop by force 
        then show "False" using k_prop def_prop y_prop poly_IVT_neg[of "r" "k" "[:f, e, d:]"] poly_IVT_pos[of "-c'/b'" "k" "[:f, e, d:]"]
          by (smt quadratic_poly_eval)
      qed
      have c2: "\<exists> (d, e, f) \<in> set b.  d * r\<^sup>2 + e * r + f = 0 \<Longrightarrow> False" 
      proof - 
        assume "\<exists> (d, e, f) \<in> set b.  d * r\<^sup>2 + e * r + f = 0"
        then obtain d' e f where def_prop: "(d', e, f) \<in> set b \<and> d' * r\<^sup>2 + e * r + f = 0"
          by auto
        then have same: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (-f/e = r)" 
        proof - 
          assume asm: "(d' = 0 \<and> e \<noteq> 0)" 
          then have " e * r + f = 0" using def_prop 
            by auto
          then show "-f/e = r" using asm
            by (metis (no_types) add.commute diff_0 divide_minus_left minus_add_cancel nonzero_mult_div_cancel_left uminus_add_conv_diff) 
        qed
        let ?r = "-f/e"
        have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> ((d', e, f) \<in> set b \<and> ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
          using same def_prop abc_prop by auto
        then have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
          by auto
        then have f1: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> False" using f5 
          by auto 
        have f2: "(d' = 0 \<and> e = 0 \<and> f = 0) \<Longrightarrow> False" proof - 
          assume "(d' = 0 \<and> e = 0 \<and> f = 0)"
          then have allzer: "\<forall>x. d'*x^2 + e*x + f = 0" by auto
          have "\<exists>y'>r. \<forall>x\<in>{r<..y'}. d' * x\<^sup>2 + e * x + f < 0"
            using b_prop def_prop  by auto
          then obtain y' where y_prop: " y' >r \<and> (\<forall>x\<in>{r<..y'}. d' * x\<^sup>2 + e * x + f < 0)" by auto
          then have "\<exists>k. k > r \<and> k < y' \<and> d' * k^2 + e * k + f < 0" using dense
            by (meson dense greaterThanAtMost_iff less_eq_real_def) 
          then show "False" using allzer
            by auto
        qed
        have f3: "d' \<noteq> 0 \<Longrightarrow> False" 
        proof - 
          assume dnonz: "d' \<noteq> 0"
          have discr: " - e\<^sup>2 + 4 * d' * f \<le> 0"
            using def_prop discriminant_negative[of d' e f] unfolding discrim_def
            using def_prop by fastforce
          then have two_cases: "r = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')
          \<or> r = (- e + 1 * sqrt (e\<^sup>2 - 4 * d' * f)) / (2 * d')"
            using def_prop dnonz discriminant_nonneg[of d' e f] unfolding discrim_def
            by fastforce
          have some_props: "((d', e, f) \<in> set b \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0)"
            using dnonz def_prop discr by auto
          let ?r1 = "(- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          let ?r2 = "(- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          have cf1: "r = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "r = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set b \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f7 by auto
          qed
          have cf2: "r = (- e +  1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "r = (- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set b \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f6 by auto
          qed
          then show "False" using two_cases cf1 cf2 by auto
        qed
          (* discriminant_nonnegative *)
        have eo: "(d' \<noteq> 0) \<or> (d' = 0 \<and> e \<noteq> 0) \<or> (d' = 0 \<and> e = 0 \<and> f = 0)" 
          using def_prop by auto
        then show "False" using f1 f2 f3 by auto
      qed
      show ?thesis using c1 c2
        by fastforce
    qed
    have d_prop: "(\<forall>(d, e, f)\<in>set d.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)" 
      using abc_prop by auto
    have h4: "(\<forall>(d, e, f)\<in>set d. d * r\<^sup>2 + e * r + f \<noteq> 0)"
    proof - 
      have "(\<exists>(d, e, f)\<in>set d. d * r\<^sup>2 + e * r + f = 0) \<Longrightarrow> False"
      proof - 
        assume "\<exists> (d, e, f) \<in> set d.  d * r\<^sup>2 + e * r + f = 0"
        then obtain d' e f where def_prop: "(d', e, f) \<in> set d \<and> d' * r\<^sup>2 + e * r + f = 0"
          by auto
        then have same: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (-f/e = r)" 
        proof - 
          assume asm: "(d' = 0 \<and> e \<noteq> 0)" 
          then have " e * r + f = 0" using def_prop 
            by auto
          then show "-f/e = r" using asm
            by (metis (no_types) add.commute diff_0 divide_minus_left minus_add_cancel nonzero_mult_div_cancel_left uminus_add_conv_diff) 
        qed
        let ?r = "-f/e"
        have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> ((d', e, f) \<in> set d \<and> ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
          using same def_prop abc_prop by auto
        then have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'> -c'/b'. \<forall>x\<in>{ -c'/b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'> -c'/b'. \<forall>x\<in>{ -c'/b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'> -c'/b'. \<forall>x\<in>{ -c'/b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'> -c'/b'. \<forall>x\<in>{ -c'/b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
          by auto
        then have f1: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> False" using f10 
          by auto 
        have f2: "(d' = 0 \<and> e = 0 \<and> f = 0) \<Longrightarrow> False" proof - 
          assume "(d' = 0 \<and> e = 0 \<and> f = 0)"
          then have allzer: "\<forall>x. d'*x^2 + e*x + f = 0" by auto
          have "\<exists>y'> r. \<forall>x\<in>{ r<..y'}. d' * x\<^sup>2 + e * x + f \<noteq> 0"
            using d_prop def_prop 
            by auto
          then obtain y' where y_prop: " y' >r \<and> (\<forall>x\<in>{r<..y'}. d' * x\<^sup>2 + e * x + f \<noteq> 0)" by auto
          then have "\<exists>k. k > r \<and> k < y' \<and> d' * k^2 + e * k + f \<noteq> 0" using dense
            by (meson dense greaterThanAtMost_iff less_eq_real_def) 
          then show "False" using allzer
            by auto
        qed
        have f3: "d' \<noteq> 0 \<Longrightarrow> False" 
        proof - 
          assume dnonz: "d' \<noteq> 0"
          have discr: " - e\<^sup>2 + 4 * d' * f \<le> 0"
            using def_prop discriminant_negative[of d' e f] unfolding discrim_def
            by fastforce
          then have two_cases: "r = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')
          \<or> r = (- e + 1 * sqrt (e\<^sup>2 - 4 * d' * f)) / (2 * d')"
            using def_prop dnonz discriminant_nonneg[of d' e f] unfolding discrim_def
            by fastforce
          have some_props: "((d', e, f) \<in> set d \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0)"
            using dnonz def_prop discr by auto
          let ?r1 = "(- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          let ?r2 = "(- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          have cf1: "r = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "r = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set d \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f12 by auto
          qed
          have cf2: "r = (- e +  1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "r = (- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set d \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f11 by auto
          qed
          then show "False" using two_cases cf1 cf2 by auto
        qed
          (* discriminant_nonnegative *)
        have eo: "(d' \<noteq> 0) \<or> (d' = 0 \<and> e \<noteq> 0) \<or> (d' = 0 \<and> e = 0 \<and> f = 0)" 
          using def_prop by auto
        then show "False" using f1 f2 f3 by auto
      qed
      then show ?thesis by auto
    qed
    have "(\<exists>(a', b', c')\<in>set c. ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * r\<^sup>2 + e * r + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * r\<^sup>2 + e * r + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * r\<^sup>2 + e * r + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * r\<^sup>2 + e * r + f \<noteq> 0))"
      using h1 h2 h3 h4 abc_prop by auto
    then show "False" using f8 by auto
  qed
  then show ?thesis by auto
qed



lemma qe_forwards_helper_lin:
  assumes alleqset: "\<forall>x. (\<forall>(d, e, f)\<in>set a. d * x^2 + e * x + f = 0)"
  assumes f5: "\<not>(\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f6: "\<not> (\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  assumes f7: "\<not> (\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f8: "\<not>(\<exists>(a', b', c')\<in>set c. (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
  assumes f10: "\<not>(\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f11: "\<not>(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  assumes f12: "\<not>(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  shows "\<not>(\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
proof - 
  have "(\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)) \<Longrightarrow> False"
  proof - 
    assume "(\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set c \<and>
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
      by auto
    then have bnonz: "b'\<noteq>0" by auto
    have h1: "(\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0)" 
      using bnonz alleqset
      by blast
    have c_prop: "(\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)" 
      using abc_prop by auto 
    have h2: "(\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0)" 
    proof - 
      have c1: "\<exists> (d, e, f) \<in> set c.  d * (- c' / b')\<^sup>2 + e * (- c' / b') + f > 0 \<Longrightarrow> False"
      proof - 
        assume "\<exists> (d, e, f) \<in> set c.  d * (- c' / b')\<^sup>2 + e * (- c' / b') + f > 0"
        then obtain d e f where def_prop: "(d, e, f) \<in> set c \<and> d * (- c' / b')\<^sup>2 + e * (- c' / b') + f > 0"
          by auto
        have "\<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0"
          using def_prop c_prop   by auto
        then obtain y' where y_prop: " y' >- c' / b' \<and> (\<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)" by auto
        have "\<exists>x\<in>{(-c'/b')<..y'}. d*x^2 + e*x + f > 0"
          using def_prop continuity_lem_gt0_expanded[of "(-c'/b')" y' d e f]
          using y_prop by linarith 
        then show "False" using  y_prop
          by auto  
      qed
      then show ?thesis
        by fastforce 
    qed
    have b_prop: "(\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0)" 
      using abc_prop by auto
    have h3: "(\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0)" 
    proof - 
      have c1: "\<exists> (d, e, f) \<in> set b.  d * (- c' / b')\<^sup>2 + e * (- c' / b') + f > 0 \<Longrightarrow> False"
      proof - 
        assume "\<exists> (d, e, f) \<in> set b.  d * (- c' / b')\<^sup>2 + e * (- c' / b') + f > 0"
        then obtain d e f where def_prop: "(d, e, f) \<in> set b \<and> d * (- c' / b')\<^sup>2 + e * (- c' / b') + f > 0"
          by auto
        then have "\<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0"
          using b_prop by auto
        then obtain y' where y_prop: " y' >- c' / b' \<and> (\<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0)" by auto
        then have "\<exists>k. k > -c'/b' \<and> k < y' \<and> d * k^2 + e * k + f < 0" using dense
          by (meson dense greaterThanAtMost_iff less_eq_real_def) 
        then obtain k where k_prop: "k > -c'/b' \<and> k < y' \<and> d * k^2 + e * k + f < 0" 
          by auto
        then have "\<not>(\<exists>x>(-c'/b'). x < y' \<and> d * x\<^sup>2 + e * x + f = 0)"
          using y_prop by force 
        then show "False" using k_prop def_prop y_prop poly_IVT_neg[of "-c'/b'" "k" "[:f, e, d:]"] poly_IVT_pos[of "-c'/b'" "k" "[:f, e, d:]"]
          by (smt quadratic_poly_eval)
      qed
      have c2: "\<exists> (d, e, f) \<in> set b.  d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0 \<Longrightarrow> False" 
      proof - 
        assume "\<exists> (d, e, f) \<in> set b.  d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0"
        then obtain d' e f where def_prop: "(d', e, f) \<in> set b \<and> d' * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0"
          by auto
        then have same: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (-f/e = -c'/b')" 
        proof - 
          assume asm: "(d' = 0 \<and> e \<noteq> 0)" 
          then have " e * (- c' / b') + f = 0" using def_prop 
            by auto
          then show "-f/e = -c'/b'" using asm 
            by auto
        qed
        let ?r = "-f/e"
        have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> ((d', e, f) \<in> set b \<and> ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
          using same def_prop abc_prop by auto
        then have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
          by auto
        then have f1: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> False" using f5 
          by auto 
        have f2: "(d' = 0 \<and> e = 0 \<and> f = 0) \<Longrightarrow> False" proof - 
          assume "(d' = 0 \<and> e = 0 \<and> f = 0)"
          then have allzer: "\<forall>x. d'*x^2 + e*x + f = 0" by auto
          have "\<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d' * x\<^sup>2 + e * x + f < 0"
            using b_prop def_prop  by auto
          then obtain y' where y_prop: " y' >- c' / b' \<and> (\<forall>x\<in>{- c' / b'<..y'}. d' * x\<^sup>2 + e * x + f < 0)" by auto
          then have "\<exists>k. k > -c'/b' \<and> k < y' \<and> d' * k^2 + e * k + f < 0" using dense
            by (meson dense greaterThanAtMost_iff less_eq_real_def) 
          then show "False" using allzer
            by auto
        qed
        have f3: "d' \<noteq> 0 \<Longrightarrow> False" 
        proof - 
          assume dnonz: "d' \<noteq> 0"
          have discr: " - e\<^sup>2 + 4 * d' * f \<le> 0"
            using def_prop discriminant_negative[of d' e f] unfolding discrim_def
            by fastforce
          then have two_cases: "(- c' / b') = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')
          \<or> (- c' / b') = (- e + 1 * sqrt (e\<^sup>2 - 4 * d' * f)) / (2 * d')"
            using def_prop dnonz discriminant_nonneg[of d' e f] unfolding discrim_def
            by fastforce
          have some_props: "((d', e, f) \<in> set b \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0)"
            using dnonz def_prop discr by auto
          let ?r1 = "(- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          let ?r2 = "(- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          have cf1: "(- c' / b') = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "(- c' / b') = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set b \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f7 by auto
          qed
          have cf2: "(- c' / b') = (- e +  1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "(- c' / b') = (- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set b \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f6 by auto
          qed
          then show "False" using two_cases cf1 cf2 by auto
        qed
          (* discriminant_nonnegative *)
        have eo: "(d' \<noteq> 0) \<or> (d' = 0 \<and> e \<noteq> 0) \<or> (d' = 0 \<and> e = 0 \<and> f = 0)" 
          using def_prop by auto
        then show "False" using f1 f2 f3 by auto
      qed
      show ?thesis using c1 c2
        by fastforce
    qed
    have d_prop: "(\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)" 
      using abc_prop by auto
    have h4: "(\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)"
    proof - 
      have "(\<exists>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<Longrightarrow> False"
        (* begin *)
      proof - 
        assume "\<exists> (d, e, f) \<in> set d.  d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0"
        then obtain d' e f where def_prop: "(d', e, f) \<in> set d \<and> d' * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0"
          by auto
        then have same: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (-f/e = -c'/b')" 
        proof - 
          assume asm: "(d' = 0 \<and> e \<noteq> 0)" 
          then have " e * (- c' / b') + f = 0" using def_prop 
            by auto
          then show "-f/e = -c'/b'" using asm 
            by auto
        qed
        let ?r = "-f/e"
        have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> ((d', e, f) \<in> set d \<and> ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
          using same def_prop abc_prop by auto
        then have "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
          by auto
        then have f1: "(d' = 0 \<and> e \<noteq> 0) \<Longrightarrow> False" using f10 
          by auto 
        have f2: "(d' = 0 \<and> e = 0 \<and> f = 0) \<Longrightarrow> False" proof - 
          assume "(d' = 0 \<and> e = 0 \<and> f = 0)"
          then have allzer: "\<forall>x. d'*x^2 + e*x + f = 0" by auto
          have "\<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d' * x\<^sup>2 + e * x + f \<noteq> 0"
            using d_prop def_prop  by auto
          then obtain y' where y_prop: " y' >- c' / b' \<and> (\<forall>x\<in>{- c' / b'<..y'}. d' * x\<^sup>2 + e * x + f \<noteq> 0)" by auto
          then have "\<exists>k. k > -c'/b' \<and> k < y' \<and> d' * k^2 + e * k + f \<noteq> 0" using dense
            by (meson dense greaterThanAtMost_iff less_eq_real_def) 
          then show "False" using allzer
            by auto
        qed
        have f3: "d' \<noteq> 0 \<Longrightarrow> False" 
        proof - 
          assume dnonz: "d' \<noteq> 0"
          have discr: " - e\<^sup>2 + 4 * d' * f \<le> 0"
            using def_prop discriminant_negative[of d' e f] unfolding discrim_def
            by fastforce
          then have two_cases: "(- c' / b') = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')
          \<or> (- c' / b') = (- e + 1 * sqrt (e\<^sup>2 - 4 * d' * f)) / (2 * d')"
            using def_prop dnonz discriminant_nonneg[of d' e f] unfolding discrim_def
            by fastforce
          have some_props: "((d', e, f) \<in> set d \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0)"
            using dnonz def_prop discr by auto
          let ?r1 = "(- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          let ?r2 = "(- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
          have cf1: "(- c' / b') = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "(- c' / b') = (- e + - 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set d \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r1. \<forall>x\<in>{?r1<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f12 by auto
          qed
          have cf2: "(- c' / b') = (- e +  1 * sqrt (e^2 - 4 * d' * f)) / (2 * d') \<Longrightarrow> False" 
          proof - 
            assume "(- c' / b') = (- e + 1 * sqrt (e^2 - 4 * d' * f)) / (2 * d')"
            then have "(d', e, f) \<in> set d \<and> d' \<noteq> 0 \<and> - e\<^sup>2 + 4 * d' * f \<le> 0 \<and> 
    ((\<forall>(d, e, f)\<in>set a. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
    (\<forall>(d, e, f)\<in>set b. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
    (\<forall>(d, e, f)\<in>set c. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
    (\<forall>(d, e, f)\<in>set d. \<exists>y'>?r2. \<forall>x\<in>{?r2<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
              using abc_prop some_props by auto
            then show "False" using f11 by auto
          qed
          then show "False" using two_cases cf1 cf2 by auto
        qed
          (* discriminant_nonnegative *)
        have eo: "(d' \<noteq> 0) \<or> (d' = 0 \<and> e \<noteq> 0) \<or> (d' = 0 \<and> e = 0 \<and> f = 0)" 
          using def_prop by auto
        then show "False" using f1 f2 f3 by auto
      qed
      then show ?thesis by auto
    qed
    have "(\<exists>(a', b', c')\<in>set c. (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
      using h1 h2 h3 h4 bnonz abc_prop by auto
    then show "False" using f8 by auto
  qed
  then show ?thesis by auto
qed



lemma qe_forwards_helper:
  assumes alleqset: "\<forall>x. (\<forall>(d, e, f)\<in>set a. d * x^2 + e * x + f = 0)"
  assumes f1: "\<not>((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0))"
  assumes f5: "\<not>(\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f6: "\<not> (\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  assumes f7: "\<not> (\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f8: "\<not>(\<exists>(a', b', c')\<in>set c. (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
  assumes f13: "\<not>(\<exists>(a', b', c')\<in>set c.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))"
  assumes f9: "\<not>(\<exists>(a', b', c')\<in>set c.  a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))"
  assumes f10: "\<not>(\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  assumes f11: "\<not>(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  assumes f12: "\<not>(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  shows "\<not>(\<exists>x. (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))" 
proof - 
  have nor: "\<forall>r. \<not>(\<exists>(a', b', c')\<in>set c. 
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         ((\<forall>(d, e, f)\<in>set a. d * r\<^sup>2 + e * r + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * r^2 + e * r + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * r^2 + e * r + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * r^2 + e * r + f \<noteq> 0)))" 
  proof clarsimp
    fix r t u v
    assume inset: "(t, u, v) \<in> set c"
    assume eo: "t = 0 \<longrightarrow> u \<noteq> 0 "
    assume zero_eq: "t*r^2 + u*r + v = 0"
    assume ah: "\<forall>x\<in>set a. case x of (d, e, f) \<Rightarrow> d * r\<^sup>2 + e * r + f = 0"
    assume bh: "\<forall>x\<in>set b. case x of (d, e, f) \<Rightarrow> d * r\<^sup>2 + e * r + f < 0" 
    assume ch: "\<forall>x\<in>set c. case x of (d, e, f) \<Rightarrow> d * r\<^sup>2 + e * r + f \<le> 0"
    assume dh: "\<forall>x\<in>set d. case x of (d, e, f) \<Rightarrow> d * r\<^sup>2 + e * r + f \<noteq> 0"
    have two_cases: "t \<noteq> 0 \<or> (t = 0 \<and> u \<noteq> 0)" using eo by auto
    have c1: "t \<noteq> 0 \<Longrightarrow> False" 
    proof - 
      assume tnonz:  "t \<noteq> 0"
      then have discr_prop: "- u\<^sup>2 + 4 * t * v \<le> 0 "
        using discriminant_negative[of t u v] zero_eq unfolding discrim_def
        by force 
      then have ris: "r =  ((-u + - 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<or>
       r = ((-u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) "
        using tnonz discriminant_nonneg[of t u v] zero_eq unfolding discrim_def by auto 
      let ?r1 = "((-u + - 1 * sqrt (u^2 - 4 * t * v)) / (2 * t))"
      let ?r2 = "((-u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t))" 
      have ris1: "r = ?r1 \<Longrightarrow> False"
      proof - 
        assume "r = ?r1"
        then have "(\<exists>(a', b', c')\<in>set c.  a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))" 
          using inset ah bh ch dh discr_prop tnonz by auto
        then show ?thesis 
          using f9 by auto
      qed
      have ris2: "r = ?r2 \<Longrightarrow> False" 
      proof - 
        assume "r = ?r2"
        then have "(\<exists>(a', b', c')\<in>set c.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))" 
          using inset ah bh ch dh discr_prop tnonz by auto
        then show ?thesis 
          using f13 by auto
      qed
      show "False" using ris ris1 ris2 by auto 
    qed
    have c2: "(t = 0 \<and> u \<noteq> 0) \<Longrightarrow> False" 
    proof - 
      assume asm: "t = 0 \<and> u \<noteq> 0"
      then have "r = -v/u" using zero_eq add.right_neutral  nonzero_mult_div_cancel_left     
        by (metis add.commute divide_divide_eq_right divide_eq_0_iff neg_eq_iff_add_eq_0)
      then have "(\<exists>(a', b', c')\<in>set c. (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
        using asm inset ah bh ch dh by auto
      then show "False" using f8
        by auto
    qed
    then show "False" using two_cases c1 c2 by auto
  qed
  have keyh: "\<And>r. \<not>(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  proof - 
    fix r
    have h8: "\<not>(\<exists>(a', b', c')\<in>set c. 
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         ((\<forall>(d, e, f)\<in>set a. d * r\<^sup>2 + e * r + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * r^2 + e * r + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * r^2 + e * r + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * r^2 + e * r + f \<noteq> 0)))" 
      using nor by auto
    show "\<not>(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*r^2 + b'*r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>r. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
      using qe_forwards_helper_gen[of c r a b d]
        alleqset  f5 f6 f7 h8 f10 f11 f12 
      by auto
  qed
  have f8a: "\<not>(\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
    using qe_forwards_helper_lin[of a b c d] alleqset f5 f6 f7 f8 f10 f11 f12
    by blast 
  have f13a: "\<not> (\<exists>(a', b', c')\<in>set c. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  proof - 
    have "(\<exists>(a', b', c')\<in>set c. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))) \<Longrightarrow> False" 
    proof - 
      assume "(\<exists>(a', b', c')\<in>set c. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
      then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set c \<and> a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))" by auto
      let ?r = "(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')"
      have somek: "\<exists>k. k = ?r" by auto
      then obtain k where k_prop: "k = ?r" by auto
      have "(a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> (a'*?r^2 + b'*?r + c' = 0)" 
        using abc_prop discriminant_nonneg[of a' b' c'] 
        unfolding discrim_def apply (auto)
        by (metis (mono_tags, lifting) times_divide_eq_right) 
      then have "(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*?r^2 + b'*?r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
        using abc_prop by auto
      then have "(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*k^2 + b'*k + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
        using k_prop by auto
      then have "\<exists>k. (\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*k^2 + b'*k + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
        by auto 
      then show "False" using keyh by auto
    qed
    then
    show ?thesis
      by auto
  qed
  have f9a: "\<not> (\<exists>(a', b', c')\<in>set c. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))" 

  proof - 
    have "(\<exists>(a', b', c')\<in>set c. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)) \<Longrightarrow> False" 
    proof - 
      assume "(\<exists>(a', b', c')\<in>set c. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
      then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set c \<and> a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)" by auto
      let ?r = "(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')"
      have somek: "\<exists>k. k = ?r" by auto
      then obtain k where k_prop: "k = ?r" by auto
      have "(a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> (a'*?r^2 + b'*?r + c' = 0)" 
        using abc_prop discriminant_nonneg[of a' b' c'] 
        unfolding discrim_def apply (auto)
        by (metis (mono_tags, lifting) times_divide_eq_right) 
      then have "(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*?r^2 + b'*?r + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>?r. \<forall>x\<in>{?r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
        using abc_prop by auto
      then have "(\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*k^2 + b'*k + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
        using k_prop by auto
      then have "\<exists>k. (\<exists>(a', b', c')\<in>set c.
         ((a'\<noteq> 0 \<or> b'\<noteq> 0) \<and> a'*k^2 + b'*k + c' = 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
        by auto 
      then show "False" using keyh by auto
    qed
    then
    show ?thesis
      by auto
  qed
    (* We need to show that the point is in one of these ranges *)
  have "(\<exists>x. (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)) \<Longrightarrow> False"
  proof - 
    assume "(\<exists>x. (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
    then obtain x where x_prop: "(\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)" by auto
    (* Need this sorted_nonzero_root_list_set in case some of the tuples from set c are (0, 0, 0) *)
    let ?srl = "sorted_nonzero_root_list_set (((set b) \<union> (set c))\<union> (set d))"
    have alleqsetvar: "\<forall>(t, u, v) \<in> set a. t = 0 \<and> u = 0 \<and> v = 0"
    proof clarsimp
      fix t u v
      assume "(t, u, v) \<in> set a"
      then have "\<forall>x. t*x^2 + u*x + v = 0" 
        using alleqset by auto 
      then have "\<forall>x\<in>{0<..1}. t * x\<^sup>2 + u * x + v = 0" 
        by auto
      then show "t = 0 \<and> u = 0 \<and> v = 0" 
        using continuity_lem_eq0[of 0 1 t u v] 
        by auto  
    qed
      (* Should violate f1 *)
    have lenzero: "length ?srl = 0 \<Longrightarrow> False"
    proof - 
      assume lenzero: "length ?srl = 0"
      have ina: "(\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0)"
        using alleqsetvar by auto 
      have inb: "(\<forall>(a, b, c)\<in>set b. \<forall>y. a * y\<^sup>2 + b * y + c < 0)"
      proof clarsimp 
        fix t u v y
        assume insetb: "(t, u, v) \<in> set b"
        then have "t * x\<^sup>2 + u * x + v < 0" using x_prop by auto
        then have tuv_prop: "t \<noteq> 0 \<or> u \<noteq> 0 \<or> v \<noteq> 0"
          by auto 
        then have tuzer: "(t = 0 \<and> u = 0) \<Longrightarrow> \<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)"
          by simp
        then have tunonz: "(t \<noteq> 0 \<or> u \<noteq> 0) \<Longrightarrow> \<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)"
        proof - 
          assume tuv_asm: "t \<noteq> 0 \<or> u \<noteq> 0"
          have "\<exists>q. t * q\<^sup>2 + u * q + v = 0 \<Longrightarrow> False"
          proof - 
            assume "\<exists> q. t * q\<^sup>2 + u * q + v = 0"
            then obtain q where "t * q\<^sup>2 + u * q + v = 0" by auto
            then have qin: "q \<in>  {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
              using insetb tuv_asm tuv_prop by auto
            have "set ?srl = nonzero_root_set (set b \<union> set c \<union> set d)"
              unfolding sorted_nonzero_root_list_set_def
              using set_sorted_list_of_set[of "nonzero_root_set (set b \<union> set c \<union> set d)"]
                nonzero_root_set_finite[of "(set b \<union> set c \<union> set d)"]
              by auto
            then have "q \<in> set ?srl" using qin unfolding nonzero_root_set_def
              by auto 
            then have "List.member ?srl q"     
              using in_set_member[of q ?srl]
              by auto
            then show "False"
              using lenzero
              by (simp add: member_rec(2)) 
          qed
          then show ?thesis by auto
        qed
        have nozer: "\<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)" 
          using  tuzer tunonz
          by blast 
        have samesn: "sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
        proof - 
          have "x < y \<Longrightarrow> sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
            using changes_sign_var[of t x u v y] nozer by auto
          have "y < x \<Longrightarrow> sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
            using changes_sign_var[of t y u v x] nozer
          proof -
            assume "y < x"
            then show ?thesis
              using \<open>\<nexists>q. t * q\<^sup>2 + u * q + v = 0\<close> \<open>sign_num (t * y\<^sup>2 + u * y + v) \<noteq> sign_num (t * x\<^sup>2 + u * x + v) \<and> y < x \<Longrightarrow> \<exists>q. t * q\<^sup>2 + u * q + v = 0 \<and> y \<le> q \<and> q \<le> x\<close> by presburger
          qed
          show ?thesis
            using changes_sign_var using \<open>x < y \<Longrightarrow> sign_num (t * x\<^sup>2 + u * x + v) = sign_num (t * y\<^sup>2 + u * y + v)\<close> \<open>y < x \<Longrightarrow> sign_num (t * x\<^sup>2 + u * x + v) = sign_num (t * y\<^sup>2 + u * y + v)\<close> 
            by fastforce 
        qed
          (* changes_sign_var *)
        have "sign_num (t*x^2 + u*x + v) = -1" using insetb unfolding sign_num_def using x_prop 
          by auto 
        then have "sign_num (t*y^2 + u*y + v) = -1" using samesn by auto
        then show "t * y\<^sup>2 + u * y + v < 0" unfolding sign_num_def
          by smt
      qed
      have inc: "(\<forall>(a, b, c)\<in>set c. \<forall>y. a * y\<^sup>2 + b * y + c \<le> 0)"
      proof clarsimp 
        fix t u v y
        assume insetc: "(t, u, v) \<in> set c"
        then have "t * x\<^sup>2 + u * x + v \<le> 0" using x_prop by auto
        then have tuzer: "t = 0 \<and> u = 0 \<Longrightarrow> t*y^2 + u*y + v \<le> 0 " 
        proof - 
          assume tandu: "t = 0 \<and> u = 0"
          then have "v \<le> 0" using insetc x_prop 
            by auto
          then show "t*y^2 + u*y + v \<le> 0" using tandu 
            by auto
        qed
        have tunonz: "t \<noteq> 0 \<or> u \<noteq> 0 \<Longrightarrow> t*y^2 + u*y + v \<le> 0"
        proof - 
          assume tuv_asm: "t \<noteq> 0 \<or> u \<noteq> 0"
          have insetcvar: "t*x^2 + u*x + v < 0" 
          proof - 
            have "t*x^2 + u*x + v = 0 \<Longrightarrow> False" 
            proof -
              assume zer: "t*x^2 + u*x + v = 0"
              then have xin: "x \<in>  {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
                using insetc tuv_asm by auto
              have "set ?srl = nonzero_root_set (set b \<union> set c \<union> set d)"
                unfolding sorted_nonzero_root_list_set_def
                using set_sorted_list_of_set[of "nonzero_root_set (set b \<union> set c \<union> set d)"]
                  nonzero_root_set_finite[of "(set b \<union> set c \<union> set d)"]
                by auto
              then have "x \<in> set ?srl" using xin unfolding nonzero_root_set_def
                by auto 
              then have "List.member ?srl x"     
                using in_set_member[of x ?srl]
                by auto
              then show "False" using lenzero
                by (simp add: member_rec(2)) 
            qed
            then show ?thesis
              using \<open>t * x\<^sup>2 + u * x + v \<le> 0\<close> by fastforce 
          qed
          then have tunonz: "\<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)"
          proof - 
            have "\<exists>q. t * q\<^sup>2 + u * q + v = 0 \<Longrightarrow> False"
            proof - 
              assume "\<exists> q. t * q\<^sup>2 + u * q + v = 0"
              then obtain q where "t * q\<^sup>2 + u * q + v = 0" by auto
              then have qin: "q \<in>  {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
                using insetc tuv_asm by auto
              have "set ?srl = nonzero_root_set (set b \<union> set c \<union> set d)"
                unfolding sorted_nonzero_root_list_set_def
                using set_sorted_list_of_set[of "nonzero_root_set (set b \<union> set c \<union> set d)"]
                  nonzero_root_set_finite[of "(set b \<union> set c \<union> set d)"]
                by auto
              then have "q \<in> set ?srl" using qin unfolding nonzero_root_set_def
                by auto 
              then have "List.member ?srl q"     
                using in_set_member[of q ?srl]
                by auto
              then show "False"
                using lenzero
                by (simp add: member_rec(2)) 
            qed
            then show ?thesis by auto
          qed
          have nozer: "\<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)" 
            using  tuzer tunonz
            by blast 
          have samesn: "sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
          proof - 
            have "x < y \<Longrightarrow> sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
              using changes_sign_var[of t x u v y] nozer by auto
            have "y < x \<Longrightarrow> sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
              using changes_sign_var[of t y u v x] nozer
            proof -
              assume "y < x"
              then show ?thesis
                using \<open>\<nexists>q. t * q\<^sup>2 + u * q + v = 0\<close> \<open>sign_num (t * y\<^sup>2 + u * y + v) \<noteq> sign_num (t * x\<^sup>2 + u * x + v) \<and> y < x \<Longrightarrow> \<exists>q. t * q\<^sup>2 + u * q + v = 0 \<and> y \<le> q \<and> q \<le> x\<close> by presburger
            qed
            show ?thesis
              using changes_sign_var using \<open>x < y \<Longrightarrow> sign_num (t * x\<^sup>2 + u * x + v) = sign_num (t * y\<^sup>2 + u * y + v)\<close> \<open>y < x \<Longrightarrow> sign_num (t * x\<^sup>2 + u * x + v) = sign_num (t * y\<^sup>2 + u * y + v)\<close> 
              by fastforce 
          qed
            (* changes_sign_var *)
          have "sign_num (t*x^2 + u*x + v) = -1" using insetcvar unfolding sign_num_def using x_prop 
            by auto 
          then have "sign_num (t*y^2 + u*y + v) = -1" using samesn by auto
          then show "t * y\<^sup>2 + u * y + v \<le> 0" unfolding sign_num_def
            by smt
        qed
        then show "t * y\<^sup>2 + u * y + v \<le> 0" 
          using tuzer tunonz
          by blast 
      qed
      have ind: "(\<forall>(a, b, c)\<in>set d. \<forall>y. a * y\<^sup>2 + b * y + c \<noteq> 0)"
      proof clarsimp 
        fix t u v y
        assume insetd: "(t, u, v) \<in> set d"
        assume falseasm: "t * y\<^sup>2 + u * y + v = 0"
        then have snz: "sign_num (t*y^2 + u*y + v) = 0"
          unfolding sign_num_def by auto
        have "t * x\<^sup>2 + u * x + v \<noteq> 0" using insetd x_prop by auto
        then have tuv_prop: "t \<noteq> 0 \<or> u \<noteq> 0 \<or> v \<noteq> 0"
          by auto 
        then have tuzer: "(t = 0 \<and> u = 0) \<Longrightarrow> \<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)"
          by simp
        then have tunonz: "(t \<noteq> 0 \<or> u \<noteq> 0) \<Longrightarrow> \<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)"
        proof - 
          assume tuv_asm: "t \<noteq> 0 \<or> u \<noteq> 0"
          have "\<exists>q. t * q\<^sup>2 + u * q + v = 0 \<Longrightarrow> False"
          proof - 
            assume "\<exists> q. t * q\<^sup>2 + u * q + v = 0"
            then obtain q where "t * q\<^sup>2 + u * q + v = 0" by auto
            then have qin: "q \<in>  {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
              using insetd tuv_asm tuv_prop by auto
            have "set ?srl = nonzero_root_set (set b \<union> set c \<union> set d)"
              unfolding sorted_nonzero_root_list_set_def
              using set_sorted_list_of_set[of "nonzero_root_set (set b \<union> set c \<union> set d)"]
                nonzero_root_set_finite[of "(set b \<union> set c \<union> set d)"]
              by auto
            then have "q \<in> set ?srl" using qin unfolding nonzero_root_set_def
              by auto 
            then have "List.member ?srl q"     
              using in_set_member[of q ?srl]
              by auto
            then show "False"
              using lenzero
              by (simp add: member_rec(2)) 
          qed
          then show ?thesis by auto
        qed
        have nozer: "\<not>(\<exists>q. t * q\<^sup>2 + u * q + v = 0)" 
          using  tuzer tunonz
          by blast 
        have samesn: "sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
        proof - 
          have "x < y \<Longrightarrow> sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
            using changes_sign_var[of t x u v y] nozer by auto
          have "y < x \<Longrightarrow> sign_num (t*x^2 + u*x + v) = sign_num (t*y^2 + u*y + v)"
            using changes_sign_var[of t y u v x] nozer
          proof -
            assume "y < x"
            then show ?thesis
              using \<open>\<nexists>q. t * q\<^sup>2 + u * q + v = 0\<close> \<open>sign_num (t * y\<^sup>2 + u * y + v) \<noteq> sign_num (t * x\<^sup>2 + u * x + v) \<and> y < x \<Longrightarrow> \<exists>q. t * q\<^sup>2 + u * q + v = 0 \<and> y \<le> q \<and> q \<le> x\<close> by presburger
          qed
          show ?thesis
            using changes_sign_var using \<open>x < y \<Longrightarrow> sign_num (t * x\<^sup>2 + u * x + v) = sign_num (t * y\<^sup>2 + u * y + v)\<close> \<open>y < x \<Longrightarrow> sign_num (t * x\<^sup>2 + u * x + v) = sign_num (t * y\<^sup>2 + u * y + v)\<close> 
            by fastforce 
        qed
          (* changes_sign_var *)
        have "sign_num (t*x^2 + u*x + v) = -1 \<or> sign_num (t*x^2 + u*x + v) = 1 " 
          using insetd unfolding sign_num_def using x_prop 
          by auto 
        then have "sign_num (t*y^2 + u*y + v) = -1 \<or> sign_num (t*y^2 + u*y + v) = 1" using samesn by auto
        then show "False"  using snz by auto 
      qed
        (* Show all the polynomials never change sign *)
      have "((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<forall>y. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<forall>y. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<forall>y. a * y\<^sup>2 + b * y + c \<noteq> 0))"
        using ina inb inc ind by auto
      then  show "False" 
        using f1
        by auto 
    qed
    have cases_mem: "(List.member ?srl x) \<Longrightarrow> False"
    proof - 
      assume "(List.member ?srl x)"
      then have "x \<in> {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
        using set_sorted_list_of_set nonzero_root_set_finite in_set_member
        by (metis List.finite_set finite_Un nonzero_root_set_def sorted_nonzero_root_list_set_def)
      then have "\<exists> (a, b, c) \<in> (((set b) \<union> (set c))\<union> (set d)) . (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a*x^2 + b*x + c = 0"
        by blast
      then obtain t u v where def_prop: "(t, u, v) \<in> (((set b) \<union> (set c))\<union> (set d)) \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> t*x^2 + u*x + v = 0"
        by auto
      have notinb: "(t, u, v) \<notin> (set b)"
      proof - 
        have "(t, u, v) \<in> (set b ) \<Longrightarrow> False"
        proof - 
          assume "(t, u, v) \<in> (set b)"
          then have "t*x^2 + u*x + v < 0" using x_prop
            by blast
          then show "False" using def_prop
            by simp 
        qed
        then  show ?thesis by auto
      qed
      have notind: "(t, u, v) \<notin> (set d)"
      proof - 
        have "(t, u, v) \<in> (set d) \<Longrightarrow> False"
        proof - 
          assume "(t, u, v) \<in> (set d)"
          then have "t*x^2 + u*x + v \<noteq> 0" using x_prop 
            by blast
          then show "False" using def_prop 
            by simp
        qed
        then show ?thesis by auto
      qed
      then have inset: "(t, u, v) \<in> (set c)"
        using def_prop notinb notind
        by blast 
      have case1: "t \<noteq> 0 \<Longrightarrow> False"
      proof - 
        assume tnonz: "t \<noteq> 0" 
        then have r1or2:"x = (- u + - 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t) \<or>
            x = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t) "
          using def_prop discriminant_negative[of t u v] discriminant_nonneg[of t u v]
          apply (auto) 
          using notinb apply (force)
           apply (simp add: discrim_def discriminant_iff)
          using notind by force 
        have discrh: "-1*u^2 + 4 * t * v \<le> 0" 
          using tnonz discriminant_negative[of t u v] unfolding discrim_def
          using def_prop by force 
        have r1: "x = (- u + - 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t) \<Longrightarrow> False"
        proof - 
          assume xis: "x = (- u + - 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)"
          have " t \<noteq> 0 \<and>
         - 1*u^2 + 4 * t * v \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
               d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * x\<^sup>2 + e * x + f \<noteq> 0)"
            using tnonz alleqset discrh x_prop
            by auto
          then have "(\<exists>(a', b', c')\<in>set c.  a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))" 
            using xis inset 
            by auto
          then show "False"
            using f9 by auto
        qed
        have r2: "x = (- u + 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t) \<Longrightarrow> False" 
        proof - 
          assume xis: "x = (- u + 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)"
          have " t \<noteq> 0 \<and>
         - 1*u^2 + 4 * t * v \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
               d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * x\<^sup>2 + e * x + f \<noteq> 0)"
            using tnonz alleqset discrh x_prop
            by auto
          then have "(\<exists>(a', b', c')\<in>set c.  a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))" 
            using xis inset 
            by auto
          then show "False"
            using f13 by auto
        qed
        then show "False"
          using r1or2 r1 r2 by auto
      qed
      have case2: "(t = 0 \<and> u \<noteq> 0) \<Longrightarrow> False" 
      proof -
        assume asm: "t = 0 \<and> u \<noteq> 0"
        then have xis: "x = - v / u" using def_prop notinb add.commute diff_0 divide_non_zero minus_add_cancel uminus_add_conv_diff
          by (metis mult_zero_left)
        have "((t = 0 \<and> u \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * x^2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * x^2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * x^2 + e * x + f \<noteq> 0))"
          using asm x_prop alleqset by auto
        then have "(\<exists>(a', b', c')\<in>set c. (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
          using xis inset
          by auto
        then show "False"
          using f8 by auto
      qed
      show "False"
        using def_prop case1 case2 by auto 
    qed
    have lengt0: "length ?srl \<ge> 1 \<Longrightarrow> False" 
    proof- 
      assume asm: "length ?srl \<ge> 1"
        (* should violate f1 *)
      have cases_lt: "x < ?srl ! 0 \<Longrightarrow> False" 
      proof - 
        assume xlt: "x < ?srl ! 0"
        have samesign: "\<forall> (a, b, c) \<in> (set b \<union> set c \<union> set d).
              (\<forall>y < x. sign_num (a * y\<^sup>2 + b * y + c) =  sign_num (a*x^2 + b*x + c))"
        proof  clarsimp  
          fix t u v y
          assume insetunion: "(t, u, v) \<in> set b \<or> (t, u, v)  \<in> set c \<or> (t, u, v) \<in> set d"
          assume ylt: "y < x" 
          have tuzer: "t = 0 \<and> u = 0 \<Longrightarrow> sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            unfolding sign_num_def 
            by auto
          have tunonzer: "t \<noteq> 0 \<or> u \<noteq> 0  \<Longrightarrow> sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
          proof - 
            assume tuv_asm: "t\<noteq> 0 \<or> u \<noteq> 0"
            have "\<not>(\<exists>q. q < ?srl ! 0 \<and> t * q\<^sup>2 + u * q + v = 0)"
            proof clarsimp 
              fix q
              assume qlt: "q < sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! 0"
              assume "t * q\<^sup>2 + u * q + v = 0"
              then have qin: "q \<in>  {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
                using insetunion tuv_asm by auto
              have "set ?srl = nonzero_root_set (set b \<union> set c \<union> set d)"
                unfolding sorted_nonzero_root_list_set_def
                using set_sorted_list_of_set[of "nonzero_root_set (set b \<union> set c \<union> set d)"]
                  nonzero_root_set_finite[of "(set b \<union> set c \<union> set d)"]
                by auto
              then have "q \<in> set ?srl" using qin unfolding nonzero_root_set_def
                by auto 
              then have lm: "List.member ?srl q"     
                using in_set_member[of q ?srl]
                by auto
              then have " List.member
                 (sorted_list_of_set (nonzero_root_set (set b \<union> set c \<union> set d)))
                 q \<Longrightarrow>
                q < sorted_list_of_set (nonzero_root_set (set b \<union> set c \<union> set d)) !
                    0 \<Longrightarrow>
                (\<And>x xs. (x \<in> set xs) = (\<exists>i<length xs. xs ! i = x)) \<Longrightarrow>
                (\<And>x xs. (x \<in> set xs) = List.member xs x) \<Longrightarrow>
                (\<And>y x. \<not> y \<le> x \<Longrightarrow> x < y) \<Longrightarrow>
                (\<And>xs. sorted xs =
                       (\<forall>i j. i \<le> j \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<le> xs ! j)) \<Longrightarrow>
                (\<And>p. sorted_nonzero_root_list_set p \<equiv>
                      sorted_list_of_set (nonzero_root_set p)) \<Longrightarrow>
                False"
              proof -
                assume a1: "List.member (sorted_list_of_set (nonzero_root_set (set b \<union> set c \<union> set d))) q"
                assume a2: "q < sorted_list_of_set (nonzero_root_set (set b \<union> set c \<union> set d)) ! 0"
                have f3: "List.member (sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)}) q"
                  using a1 by (metis nonzero_root_set_def)
                have f4: "q < sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)} ! 0"
                  using a2 by (metis nonzero_root_set_def)
                have f5: "q \<in> set (sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)})"
                  using f3 by (meson in_set_member)
                have "\<forall>rs r. \<exists>n. ((r::real) \<notin> set rs \<or> n < length rs) \<and> (r \<notin> set rs \<or> rs ! n = r)"
                  by (metis in_set_conv_nth)
                then obtain nn :: "real list \<Rightarrow> real \<Rightarrow> nat" where
                  f6: "\<And>r rs. (r \<notin> set rs \<or> nn rs r < length rs) \<and> (r \<notin> set rs \<or> rs ! nn rs r = r)"
                  by moura
                then have "sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)} ! nn (sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)}) q = q"
                  using f5 by blast
                then have "\<And>n. \<not> sorted (sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)}) \<or> \<not> n \<le> nn (sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)}) q \<or> \<not> nn (sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)}) q < length (sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)}) \<or> sorted_list_of_set {r. \<exists>p. p \<in> set b \<union> set c \<union> set d \<and> (case p of (ra, rb, rc) \<Rightarrow> (ra \<noteq> 0 \<or> rb \<noteq> 0) \<and> ra * r\<^sup>2 + rb * r + rc = 0)} ! n \<le> q"
                  using not_less not_less0 sorted_iff_nth_mono
                  by (metis (no_types, lifting)) 
                then show ?thesis
                  using f6 f5 f4 by (meson le0 not_less sorted_sorted_list_of_set)
              qed 
              then show "False" using lm qlt in_set_conv_nth in_set_member not_le_imp_less not_less0 sorted_iff_nth_mono sorted_nonzero_root_list_set_def sorted_sorted_list_of_set
                by auto
            qed   
            then have "\<not>(\<exists>q. q \<le> x \<and> t * q\<^sup>2 + u * q + v = 0)"
              using xlt
              by auto 
            then show " sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
              using ylt changes_sign_var[of t y u v x]
              by blast
          qed
          then show " sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            using tuzer 
            by blast
        qed
        have bseth: "(\<forall>(a, b, c)\<in>set b. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0)" 
        proof clarsimp 
          fix t u v y
          assume insetb: "(t, u, v) \<in> set b"
          assume yltx: "y < x" 
          have "(t, u, v) \<in> (set b \<union> set c \<union> set d)" using insetb 
            by auto
          then have samesn: "sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            using samesign insetb yltx
            by blast 
          have "sign_num (t*x^2 + u*x + v) = -1" 
            using x_prop insetb unfolding sign_num_def
            by auto
          then show  "t * y\<^sup>2 + u * y + v < 0"
            using samesn unfolding sign_num_def 
            by (metis add.right_inverse add.right_neutral linorder_neqE_linordered_idom one_add_one zero_neq_numeral) 
        qed
        have bset: " (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0)"
        proof clarsimp 
          fix t u v
          assume inset: "(t, u, v) \<in> set b"
          then have " \<forall>y<x. t * y\<^sup>2 + u * y + v < 0 " using bseth by auto
          then show "\<exists>x. \<forall>y<x. t * y\<^sup>2 + u * y + v < 0"
            by auto
        qed
        have cseth: "(\<forall>(a, b, c)\<in>set c. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0)" 
        proof clarsimp 
          fix t u v y
          assume insetc: "(t, u, v) \<in> set c"
          assume yltx: "y < x" 
          have "(t, u, v) \<in> (set b \<union> set c \<union> set d)" using insetc
            by auto
          then have samesn: "sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            using samesign insetc yltx
            by blast 
          have "sign_num (t*x^2 + u*x + v) = -1 \<or> sign_num (t*x^2 + u*x + v) = 0" 
            using x_prop insetc unfolding sign_num_def
            by auto
          then show  "t * y\<^sup>2 + u * y + v \<le> 0"
            using samesn unfolding sign_num_def
            using zero_neq_one by fastforce
        qed
        have cset: " (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0)"
        proof clarsimp 
          fix t u v
          assume inset: "(t, u, v) \<in> set c"
          then have " \<forall>y<x. t * y\<^sup>2 + u * y + v \<le> 0 " using cseth by auto
          then show "\<exists>x. \<forall>y<x. t * y\<^sup>2 + u * y + v \<le>0"
            by auto
        qed
        have dseth: "(\<forall>(a, b, c)\<in>set d. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0)" 
        proof clarsimp 
          fix t u v y
          assume insetd: "(t, u, v) \<in> set d"
          assume yltx: "y < x" 
          assume contrad: "t * y\<^sup>2 + u * y + v = 0"
          have "(t, u, v) \<in> (set b \<union> set c \<union> set d)" using insetd
            by auto
          then have samesn: "sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            using samesign insetd yltx
            by blast 
          have "sign_num (t*x^2 + u*x + v) = -1 \<or> sign_num (t*x^2 + u*x + v) = 1" 
            using x_prop insetd unfolding sign_num_def
            by auto
          then have  "t * y\<^sup>2 + u * y + v \<noteq> 0"
            using samesn unfolding sign_num_def 
            by auto
          then show "False" using contrad by auto
        qed
        have dset: " (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0)"
        proof clarsimp 
          fix t u v
          assume inset: "(t, u, v) \<in> set d"
          then have " \<forall>y<x. t * y\<^sup>2 + u * y + v \<noteq> 0 " using dseth by auto
          then show "\<exists>x. \<forall>y<x. t * y\<^sup>2 + u * y + v \<noteq> 0"
            by auto
        qed
        have "(\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0)" 
          using alleqsetvar by auto 
        then have "((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0))" 
          using  bset cset dset by auto
        then show "False" using f1 by auto
      qed
        (* should violate one of the infinitesmials *)
      have cases_gt: " x > ?srl ! (length ?srl - 1) \<Longrightarrow> False" 
      proof - 
        assume xgt: "x > ?srl ! (length ?srl - 1)"
        let ?bgrt = "?srl ! (length ?srl - 1)"
        have samesign: "\<forall> (a, b, c) \<in> (set b \<union> set c \<union> set d).
              (\<forall>y > ?bgrt. sign_num (a * y\<^sup>2 + b * y + c) =  sign_num (a*x^2 + b*x + c))"
        proof  clarsimp  
          fix t u v y
          assume insetunion: "(t, u, v) \<in> set b \<or> (t, u, v)  \<in> set c \<or> (t, u, v) \<in> set d"
          assume ygt: "sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
              (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0)  < y" 
          have tuzer: "t = 0 \<and> u = 0 \<Longrightarrow> sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            unfolding sign_num_def 
            by auto
          have tunonzer: "t \<noteq> 0 \<or> u \<noteq> 0  \<Longrightarrow> sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
          proof - 
            assume tuv_asm: "t\<noteq> 0 \<or> u \<noteq> 0"
            have "\<not>(\<exists>q. q > ?srl ! (length ?srl - 1) \<and> t * q\<^sup>2 + u * q + v = 0)"
            proof clarsimp 
              fix q
              assume qgt: "sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
                (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0) < q"
              assume "t * q\<^sup>2 + u * q + v = 0"
              then have qin: "q \<in>  {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
                using insetunion tuv_asm by auto
              have "set ?srl = nonzero_root_set (set b \<union> set c \<union> set d)"
                unfolding sorted_nonzero_root_list_set_def
                using set_sorted_list_of_set[of "nonzero_root_set (set b \<union> set c \<union> set d)"]
                  nonzero_root_set_finite[of "(set b \<union> set c \<union> set d)"]
                by auto
              then have "q \<in> set ?srl" using qin unfolding nonzero_root_set_def
                by auto 
              then have "List.member ?srl q"     
                using in_set_member[of q ?srl]
                by auto
              then show "False" using qgt in_set_conv_nth in_set_member not_le_imp_less not_less0 sorted_iff_nth_mono sorted_nonzero_root_list_set_def sorted_sorted_list_of_set
                by (smt (z3) Suc_diff_Suc Suc_n_not_le_n \<open>q \<in> set (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d))\<close> in_set_conv_nth length_0_conv length_greater_0_conv length_sorted_list_of_set lenzero less_Suc_eq_le minus_nat.diff_0 not_le sorted_nth_mono sorted_sorted_list_of_set) 
            qed   
            then have nor: "\<not>(\<exists>q. q > ?bgrt \<and> t * q\<^sup>2 + u * q + v = 0)"
              using xgt
              by auto 
            have c1: " x > y \<Longrightarrow>  sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
              using nor changes_sign_var[of t y u v x] xgt ygt
              by fastforce 
            then have c2: " y > x \<Longrightarrow>  sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
              using nor changes_sign_var[of t x u v y] xgt ygt
              by force
            then have c3: " x = y \<Longrightarrow>  sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
              unfolding sign_num_def 
              by auto
            then show "sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
              using c1 c2 c3
              by linarith
          qed
          then show " sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            using tuzer 
            by blast
        qed

        have "(\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0)" 
          using alleqsetvar by auto 
        have " ?bgrt \<in> set ?srl" 
          using set_sorted_list_of_set nonzero_root_set_finite in_set_member
          using asm by auto
        then have "?bgrt \<in> nonzero_root_set (set b \<union> set c \<union> set d )"
          unfolding sorted_nonzero_root_list_set_def
          using  set_sorted_list_of_set nonzero_root_set_finite 
          by auto
        then have "\<exists>t u v. (t, u, v) \<in> set b \<union> set c \<union> set d \<and>(t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)"
          unfolding nonzero_root_set_def by auto
        then obtain t u v where tuvprop1: "(t, u, v) \<in> set b \<union> set c \<union> set d \<and>(t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)"
          by auto
        then have tuvprop: "((t, u, v) \<in> set b \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0))
          \<or> ((t, u, v) \<in> set c \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<or>
            ((t, u, v) \<in> set d \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0))  "
          by auto
        have tnonz: "t\<noteq> 0 \<Longrightarrow> (-1*u^2 + 4 * t * v \<le> 0  \<and> (?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t) \<or> ?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)))"
        proof - 
          assume "t\<noteq> 0"
          have "-1*u^2 + 4 * t * v \<le> 0 "  using tuvprop1 discriminant_negative[of t u v]
            unfolding discrim_def
            using \<open>t \<noteq> 0\<close> by force              
          then show ?thesis
            using tuvprop discriminant_nonneg[of t u v]
            unfolding discrim_def
            using \<open>t \<noteq> 0\<close> by auto 
        qed
        have unonz: "(t = 0 \<and> u \<noteq> 0) \<Longrightarrow> ?bgrt = - v / u"
        proof - 
          assume "(t = 0 \<and> u \<noteq> 0)"
          then have "u*?bgrt + v = 0" using tuvprop1
            by simp 
          then show "?bgrt = - v / u"
            by (simp add: \<open>t = 0 \<and> u \<noteq> 0\<close> eq_minus_divide_eq mult.commute) 
        qed

        have allpropb: "(\<forall>(d, e, f)\<in>set b.
              \<forall>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0)" 
        proof clarsimp 
          fix t1 u1 v1 y1 x1
          assume ins: "(t1, u1, v1) \<in> set b"
          assume x1gt: " sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
       (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0) < x1"
          assume "x1 \<le> y1"
          have xsn: "sign_num (t1 * x^2 + u1 * x + v1 ) = -1" using ins x_prop unfolding sign_num_def
            by auto
          have "sign_num (t1 * x1\<^sup>2 + u1 * x1 + v1 ) = sign_num (t1 * x^2 + u1 * x + v1 ) " 
            using ins x1gt samesign
            apply (auto) 
            by blast 
          then show "t1 * x1\<^sup>2 + u1 * x1 + v1 < 0" using xsn unfolding sign_num_def
            by (metis add.right_inverse add.right_neutral linorder_neqE_linordered_idom one_add_one zero_neq_numeral) 
        qed
        have allpropbvar: "(\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0)" 
        proof clarsimp 
          fix t1 u1 v1
          assume "(t1, u1, v1) \<in> set b"
          then have "\<forall>x\<in>{?bgrt<..(?bgrt + 1)}. t1 * x\<^sup>2 + u1 * x + v1 < 0"
            using allpropb
            by force 
          then show "\<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
           (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0).
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
               (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0)<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 < 0"
            using less_add_one
            by (metis One_nat_def)        
        qed
        have allpropc: "(\<forall>(d, e, f)\<in>set c.
              \<forall>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)" 
        proof clarsimp 
          fix t1 u1 v1 y1 x1
          assume ins: "(t1, u1, v1) \<in> set c"
          assume x1gt: " sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
       (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0) < x1"
          assume "x1 \<le> y1"
          have xsn: "sign_num (t1 * x^2 + u1 * x + v1 ) = -1 \<or> sign_num (t1 * x^2 + u1 * x + v1 ) = 0" using ins x_prop unfolding sign_num_def
            by auto
          have "sign_num (t1 * x1\<^sup>2 + u1 * x1 + v1 ) = sign_num (t1 * x^2 + u1 * x + v1 ) " 
            using ins x1gt samesign  One_nat_def
          proof -
            have "case (t1, u1, v1) of (r, ra, rb) \<Rightarrow> \<forall>raa>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 1). sign_num (r * raa\<^sup>2 + ra * raa + rb) = sign_num (r * x\<^sup>2 + ra * x + rb)"
              by (smt (z3) Un_iff ins samesign)
            then show ?thesis
              by (simp add: x1gt)
          qed
          then show "t1 * x1\<^sup>2 + u1 * x1 + v1 \<le> 0" using xsn unfolding sign_num_def
            by (metis equal_neg_zero less_numeral_extra(3) linorder_not_less zero_neq_one)
        qed
        have allpropcvar: "(\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)" 
        proof clarsimp 
          fix t1 u1 v1
          assume "(t1, u1, v1) \<in> set c"
          then have "\<forall>x\<in>{?bgrt<..(?bgrt + 1)}. t1 * x\<^sup>2 + u1 * x + v1 \<le> 0"
            using allpropc
            by force 
          then show "\<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
           (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0).
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
               (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0)<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 \<le> 0"
            using less_add_one One_nat_def
            by (metis (no_types, hide_lams))        
        qed
        have allpropd: "(\<forall>(d, e, f)\<in>set d.
              \<forall>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)" 
        proof clarsimp 
          fix t1 u1 v1 y1 x1
          assume ins: "(t1, u1, v1) \<in> set d"
          assume contrad:"t1 * x1\<^sup>2 + u1 * x1 + v1 = 0"
          assume x1gt: " sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
       (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0) < x1"
          assume "x1 \<le> y1"
          have xsn: "sign_num (t1 * x^2 + u1 * x + v1 ) = -1 \<or> sign_num (t1 * x^2 + u1 * x + v1 ) = 1" using ins x_prop unfolding sign_num_def
            by auto
          have "sign_num (t1 * x1\<^sup>2 + u1 * x1 + v1 ) = sign_num (t1 * x^2 + u1 * x + v1 ) " 
            using ins x1gt samesign apply (auto) 
            by blast 
          then have "t1 * x1\<^sup>2 + u1 * x1 + v1 \<noteq> 0" using xsn unfolding sign_num_def 
            by auto
          then show "False" using contrad by auto
        qed
        have allpropdvar: "(\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)" 
        proof clarsimp 
          fix t1 u1 v1
          assume "(t1, u1, v1) \<in> set d"
          then have "\<forall>x\<in>{?bgrt<..(?bgrt + 1)}. t1 * x\<^sup>2 + u1 * x + v1 \<noteq> 0"
            using allpropd
            by force 
          then show "\<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
           (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0).
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
               (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0)<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 \<noteq> 0"
            using less_add_one
            by (metis (no_types, hide_lams) One_nat_def)     
        qed
        have "\<forall>x. (\<forall>(d, e, f)\<in>set a.
             d * x\<^sup>2 + e * x + f = 0)" using alleqsetvar
          by auto
        then have ast: "(\<forall>(d, e, f)\<in>set a.
             \<forall>x\<in>{?bgrt<..(?bgrt + 1)}. d * x\<^sup>2 + e * x + f = 0)"
          by auto
        have allpropavar: "(\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0)"
        proof clarsimp 
          fix t1 u1 v1 
          assume "(t1, u1, v1) \<in> set a"
          then have "\<forall>x\<in>{?bgrt<..(?bgrt + 1)}. t1 * x\<^sup>2 + u1 * x + v1 = 0 "
            using ast by auto 
          then show "\<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
           (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0).
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) !
               (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - Suc 0)<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 = 0"
            using less_add_one One_nat_def
            by metis
        qed
        have quadsetb: "((t, u, v) \<in> set b \<and> t\<noteq> 0) \<Longrightarrow> False"
        proof - 
          assume asm: "(t, u, v) \<in> set b \<and> t\<noteq> 0"
          have bgrt1: "(?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
          proof - 
            assume bgrtis: "?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
            have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
              using \<open>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 1) = (- u + 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)\<close> 
              by auto 
            have "((t, u, v)\<in>set b \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using f6 bgrtis 
              by auto
          qed
          have bgrt2: "(?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
          proof -
            assume bgrtis: "?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
            have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
              using \<open>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 1) = (- u + -1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)\<close> 
              by auto
            have "((t, u, v)\<in>set b \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using f7 bgrtis 
              by auto
          qed 
          show "False" using tnonz bgrt1 bgrt2 asm 
            by auto
        qed
        have linsetb: "((t, u, v) \<in> set b \<and> (t = 0 \<and> u \<noteq> 0)) \<Longrightarrow> False"
        proof - 
          assume asm: "(t, u, v) \<in> set b \<and> (t = 0 \<and> u \<noteq> 0)"
          then have bgrtis: "?bgrt = (- v / u)"
            using unonz
            by blast 
          have "((t, u, v)\<in>set b \<and> (t = 0 \<and> u \<noteq> 0) \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
            using asm allpropavar allpropbvar allpropcvar allpropdvar
            by linarith
          then show "False" using bgrtis f5  
            by auto
        qed
        have insetb: "((t, u, v) \<in> set b \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<Longrightarrow> False"
          using quadsetb linsetb by auto
        have quadsetc: "(t, u, v) \<in> set c \<and> t\<noteq> 0 \<Longrightarrow> False"
        proof - 
          assume asm: "(t, u, v) \<in> set c \<and> t\<noteq> 0"
          have bgrt1: "(?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
          proof - 
            assume bgrtis: "?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
            have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
              using \<open>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 1) = (- u + 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)\<close> 
              by auto 
            have "((t, u, v)\<in>set c \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using f13a bgrtis 
              by auto
          qed
          have bgrt2: "(?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
          proof -
            assume bgrtis: "?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
            have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
              using \<open>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 1) = (- u + -1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)\<close> 
              by auto
            have "((t, u, v)\<in>set c \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using f9a bgrtis 
              by auto
          qed 
          show "False" using tnonz bgrt1 bgrt2 asm 
            by auto
        qed
        have linsetc: "(t, u, v) \<in> set c \<and> (t = 0 \<and> u \<noteq> 0) \<Longrightarrow> False"
        proof - 
          assume asm: "(t, u, v) \<in> set c \<and> (t = 0 \<and> u \<noteq> 0)"
          then have bgrtis: "?bgrt = (- v / u)"
            using unonz
            by blast 
          have "((t, u, v)\<in>set c \<and> (t = 0 \<and> u \<noteq> 0) \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
            using asm allpropavar allpropbvar allpropcvar allpropdvar
            by linarith
          then show "False" using bgrtis f8a  
            by auto
        qed
        have insetc: "((t, u, v) \<in> set c \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<Longrightarrow> False"
          using quadsetc linsetc by auto
        have quadsetd: "(t, u, v) \<in> set d \<and> t\<noteq> 0 \<Longrightarrow> False"
        proof - 
          assume asm: "(t, u, v) \<in> set d \<and> t\<noteq> 0"
          have bgrt1: "(?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
          proof - 
            assume bgrtis: "?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
            have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
              using \<open>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 1) = (- u + 1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)\<close> 
              by auto 
            have "((t, u, v)\<in>set d \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using f11 bgrtis 
              by auto
          qed
          have bgrt2: "(?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
          proof -
            assume bgrtis: "?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
            have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
              using \<open>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! (length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 1) = (- u + -1 * sqrt (u\<^sup>2 - 4 * t * v)) / (2 * t)\<close> 
              by auto
            have "((t, u, v)\<in>set d \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using f12 bgrtis 
              by auto
          qed 
          show "False" using tnonz bgrt1 bgrt2 asm 
            by auto
        qed
        have linsetd: "(t, u, v) \<in> set d \<and> (t = 0 \<and> u \<noteq> 0) \<Longrightarrow> False"
        proof - 
          assume asm: "(t, u, v) \<in> set d \<and> (t = 0 \<and> u \<noteq> 0)"
          then have bgrtis: "?bgrt = (- v / u)"
            using unonz
            by blast 
          have "((t, u, v)\<in>set d \<and> (t = 0 \<and> u \<noteq> 0) \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
            using asm allpropavar allpropbvar allpropcvar allpropdvar
            by linarith
          then show "False" using bgrtis f10
            by auto
        qed
        have insetd: "((t, u, v) \<in> set d \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<Longrightarrow> False"
          using quadsetd linsetd by auto
        then show "False" using insetb insetc insetd tuvprop 
          by auto
      qed
      have len1: "length ?srl = 1 \<Longrightarrow> False" 
      proof - 
        assume len1: "length ?srl = 1"
        have cases: "(List.member ?srl x) \<or> x < ?srl ! 0 \<or> x > ?srl ! 0"
          using in_set_member lenzero nth_mem by fastforce
        then show "False"
          using len1 cases_mem cases_lt cases_gt by auto
      qed
      have lengtone: "length ?srl > 1 \<Longrightarrow> False" 
      proof - 
        assume lengt1: "length ?srl > 1" 
        have cases: "(List.member ?srl x) \<or> x < ?srl ! 0 \<or> x > ?srl ! (length ?srl -1)
                  \<or> (\<exists>k \<le> (length ?srl - 2). (?srl ! k < x \<and> x <?srl ! (k + 1)))"
        proof -
          have eo: "x < ?srl ! 0 \<or> x > ?srl ! (length ?srl -1) \<or> (x \<ge> ?srl ! 0 \<and> x \<le> ?srl ! (length ?srl -1))"
            by auto
          have ifo: "(x \<ge> ?srl ! 0 \<and> x \<le> ?srl ! (length ?srl -1)) \<Longrightarrow> ((List.member ?srl x) \<or> (\<exists>k \<le> (length ?srl - 2). ?srl ! k < x \<and> x <?srl ! (k + 1)))"
          proof - 
            assume xinbtw: "x \<ge> ?srl ! 0 \<and> x \<le> ?srl ! (length ?srl -1)"
            then have "\<not>(List.member ?srl x) \<Longrightarrow>  (\<exists>k \<le> (length ?srl - 2). ?srl ! k < x \<and> x <?srl ! (k + 1))"
            proof - 
              assume nonmem: "\<not>(List.member ?srl x)"
              have "\<not>(\<exists>k \<le> (length ?srl - 2). ?srl ! k < x \<and> x <?srl ! (k + 1)) \<Longrightarrow> False"
              proof clarsimp
                assume "\<forall>k. sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < x \<longrightarrow>
        k \<le> length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 2 \<longrightarrow>
        \<not> x < sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! Suc k"
                then have allk: "(\<forall>k \<le> length ?srl - 2. ?srl ! k < x \<longrightarrow>
        \<not> x < ?srl ! Suc k)" by auto 
                have basec: "x \<ge> ?srl ! 0" using xinbtw by auto
                have "\<forall>k \<le> length ?srl - 2. ?srl ! k < x" 
                proof clarsimp 
                  fix k
                  assume klteq: "k \<le> length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 2"
                  show "sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < x"
                    using nonmem klteq basec 
                  proof (induct k)
                    case 0
                    then show ?case
                      using in_set_member lenzero nth_mem by fastforce 
                  next
                    case (Suc k)
                    then show ?case
                      by (smt Suc_leD Suc_le_lessD \<open>\<forall>k. sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < x \<longrightarrow> k \<le> length (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d)) - 2 \<longrightarrow> \<not> x < sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! Suc k\<close> diff_less in_set_member length_0_conv length_greater_0_conv lenzero less_trans_Suc nth_mem pos2) 
                  qed
                qed
                then have "x \<ge> ?srl ! (length ?srl -1)" 
                  using allk
                  by (metis One_nat_def Suc_diff_Suc lengt1 less_eq_real_def less_or_eq_imp_le one_add_one plus_1_eq_Suc xinbtw) 
                then have "x > ?srl ! (length ?srl - 1)" using nonmem
                  by (metis One_nat_def Suc_le_D asm diff_Suc_Suc diff_zero in_set_member lessI less_eq_real_def nth_mem) 
                then show "False" using xinbtw by auto
              qed
              then show "(\<exists>k \<le> (length ?srl - 2). ?srl ! k < x \<and> x <?srl ! (k + 1))"
                by blast
            qed
            then show "((List.member ?srl x) \<or> (\<exists>k \<le> (length ?srl - 2). ?srl ! k < x \<and> x <?srl ! (k + 1)))" 
              using sorted_nth_mono
              by auto 
          qed
          then show ?thesis using eo ifo by auto
        qed
          (* should violate one of the infinitesmials *)
        have cases_btw: "(\<exists>k \<le> (length ?srl - 2). ?srl ! k < x \<and> x <?srl ! (k + 1)) \<Longrightarrow> False"
        proof - 
          assume "(\<exists>k \<le> (length ?srl - 2). ?srl ! k < x \<and> x <?srl ! (k + 1))"
          then obtain k where k_prop: "k \<le> (length ?srl - 2) \<and> ?srl ! k < x \<and> x <?srl ! (k + 1)"
            by auto
          have samesign: "\<forall> (a, b, c) \<in> (set b \<union> set c \<union> set d).
              (\<forall>y. (?srl ! k < y \<and> y <?srl ! (k + 1)) \<longrightarrow> sign_num (a * y\<^sup>2 + b * y + c) =  sign_num (a*x^2 + b*x + c))"
          proof  clarsimp  
            fix t u v y
            assume insetunion: "(t, u, v) \<in> set b \<or> (t, u, v)  \<in> set c \<or> (t, u, v) \<in> set d"
            assume ygt: " sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < y" 
            assume ylt: "y < sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! Suc k"
            have tuzer: "t = 0 \<and> u = 0 \<Longrightarrow> sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
              unfolding sign_num_def 
              by auto
            have tunonzer: "t \<noteq> 0 \<or> u \<noteq> 0  \<Longrightarrow> sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
            proof - 
              assume tuv_asm: "t\<noteq> 0 \<or> u \<noteq> 0"
              have nor: "\<not>(\<exists>q. q > ?srl ! k \<and> q < ?srl ! (k + 1) \<and> t * q\<^sup>2 + u * q + v = 0)"
              proof clarsimp 
                fix q
                assume qlt: "q < sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! Suc k"
                assume qgt: "sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < q"
                assume "t * q\<^sup>2 + u * q + v = 0"
                then have qin: "q \<in>  {x. \<exists>(a, b, c)\<in>set b \<union> set c \<union> set d. (a \<noteq> 0 \<or> b \<noteq> 0) \<and> a * x\<^sup>2 + b * x + c = 0}"
                  using insetunion tuv_asm by auto
                have "set ?srl = nonzero_root_set (set b \<union> set c \<union> set d)"
                  unfolding sorted_nonzero_root_list_set_def
                  using set_sorted_list_of_set[of "nonzero_root_set (set b \<union> set c \<union> set d)"]
                    nonzero_root_set_finite[of "(set b \<union> set c \<union> set d)"]
                  by auto
                then have "q \<in> set ?srl" using qin unfolding nonzero_root_set_def
                  by auto 
                then have "List.member ?srl q"     
                  using in_set_member[of q ?srl]
                  by auto
                then have "\<exists>n < length ?srl. q = ?srl ! n"
                  by (metis \<open>q \<in> set (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d))\<close> in_set_conv_nth) 
                then obtain n where nprop: "n < length ?srl \<and> q = ?srl ! n" by auto
                then have ngtk: "n > k"
                proof - 
                  have sortedh: "sorted ?srl"
                    by (simp add: sorted_nonzero_root_list_set_def) 
                  then have nlteq: "n \<le> k \<Longrightarrow> ?srl ! n \<le> ?srl ! k" using nprop k_prop sorted_iff_nth_mono
                    using sorted_nth_mono
                    by (metis (no_types, hide_lams) Suc_1 \<open>q \<in> set (sorted_nonzero_root_list_set (set b \<union> set c \<union> set d))\<close> diff_Suc_less length_pos_if_in_set sup.absorb_iff2 sup.strict_boundedE) 
                  have "?srl ! n > ?srl ! k" using nprop qgt by auto
                  then show ?thesis
                    using nlteq
                    by linarith 
                qed
                then have nltkp1: "n < k+1"
                proof - 
                  have sortedh: "sorted ?srl"
                    by (simp add: sorted_nonzero_root_list_set_def) 
                  then have ngteq: "k+1 \<le> n \<Longrightarrow> ?srl ! (k+1) \<le> ?srl ! n" using nprop k_prop sorted_iff_nth_mono
                    by auto
                  have "?srl ! n < ?srl ! (k + 1)" using nprop qlt by auto
                  then show ?thesis
                    using ngteq by linarith
                qed
                then show "False" using ngtk nltkp1 by auto
              qed
              have c1: " x > y \<Longrightarrow>  sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
                using nor changes_sign_var[of t y u v x] k_prop ygt ylt
                by fastforce 
              then have c2: " y > x \<Longrightarrow>  sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
                using nor changes_sign_var[of t x u v y] k_prop ygt ylt
                by force
              then have c3: " x = y \<Longrightarrow>  sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
                unfolding sign_num_def 
                by auto
              then show "sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
                using c1 c2 c3
                by linarith
            qed
            then show " sign_num (t * y\<^sup>2 + u * y + v) = sign_num (t * x\<^sup>2 + u * x + v)"
              using tuzer 
              by blast
          qed

          let ?bgrt = "?srl ! k"

          have "(\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0)" 
            using alleqsetvar by auto 
          have " ?bgrt \<in> set ?srl" 
            using set_sorted_list_of_set nonzero_root_set_finite in_set_member k_prop asm
            by (smt diff_Suc_less le_eq_less_or_eq less_le_trans nth_mem one_add_one plus_1_eq_Suc zero_less_one)
          then have "?bgrt \<in> nonzero_root_set (set b \<union> set c \<union> set d )"
            unfolding sorted_nonzero_root_list_set_def
            using  set_sorted_list_of_set nonzero_root_set_finite 
            by auto
          then have "\<exists>t u v. (t, u, v) \<in> set b \<union> set c \<union> set d \<and>(t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)"
            unfolding nonzero_root_set_def by auto
          then obtain t u v where tuvprop1: "(t, u, v) \<in> set b \<union> set c \<union> set d \<and>(t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)"
            by auto
          then have tuvprop: "((t, u, v) \<in> set b \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0))
          \<or> ((t, u, v) \<in> set c \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<or>
            ((t, u, v) \<in> set d \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0))  "
            by auto
          have tnonz: "t\<noteq> 0 \<Longrightarrow> (-1*u^2 + 4 * t * v \<le> 0  \<and> (?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t) \<or> ?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)))"
          proof - 
            assume "t\<noteq> 0"
            have "-1*u^2 + 4 * t * v \<le> 0 "  using tuvprop1 discriminant_negative[of t u v]
              unfolding discrim_def
              using \<open>t \<noteq> 0\<close> by force              
            then show ?thesis
              using tuvprop discriminant_nonneg[of t u v]
              unfolding discrim_def
              using \<open>t \<noteq> 0\<close> by auto 
          qed
          have unonz: "(t = 0 \<and> u \<noteq> 0) \<Longrightarrow> ?bgrt = - v / u"
          proof - 
            assume "(t = 0 \<and> u \<noteq> 0)"
            then have "u*?bgrt + v = 0" using tuvprop1
              by simp 
            then show "?bgrt = - v / u"
              by (simp add: \<open>t = 0 \<and> u \<noteq> 0\<close> eq_minus_divide_eq mult.commute) 
          qed

          have "\<exists>y'. y' > x \<and> y' < ?srl ! (k+1)" using k_prop dense
            by blast 
          then obtain y1 where y1_prop: "y1 > x \<and> y1 < ?srl ! (k+1)" by auto
          then have y1inbtw: "y1 > ?srl ! k \<and> y1 < ?srl ! (k+1)" using k_prop
            by auto

          have allpropb: "(\<forall>(d, e, f)\<in>set b.
             \<forall>x\<in>{?bgrt<..y1}. d * x\<^sup>2 + e * x + f < 0)" 
          proof clarsimp 
            fix t1 u1 v1 x1
            assume ins: "(t1, u1, v1) \<in> set b"
            assume x1gt: "sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < x1"
            assume x1lt: "x1 \<le> y1"
            have x1inbtw: "x1 > ?srl ! k \<and> x1 < ?srl ! (k+1)"
              using x1gt x1lt y1inbtw
              by (smt One_nat_def cases_gt k_prop) 
            have xsn: "sign_num (t1 * x^2 + u1 * x + v1 ) = -1" using ins x_prop unfolding sign_num_def
              by auto
            have "sign_num (t1 * x1\<^sup>2 + u1 * x1 + v1 ) = sign_num (t1 * x^2 + u1 * x + v1 ) " 
              using ins x1inbtw samesign
              by blast 
            then show "t1 * x1\<^sup>2 + u1 * x1 + v1 < 0" using xsn unfolding sign_num_def 
              by (metis add.right_inverse add.right_neutral linorder_neqE_linordered_idom one_add_one zero_neq_numeral) 
          qed
          have allpropbvar: "(\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0)" 
          proof clarsimp 
            fix t1 u1 v1
            assume "(t1, u1, v1) \<in> set b"
            then have "\<forall>x\<in>{?bgrt<..y1}. t1 * x\<^sup>2 + u1 * x + v1 < 0"
              using allpropb
              by force 
            then show " \<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k.
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 < 0" 
              using y1inbtw by blast 
          qed
          have allpropc: "(\<forall>(d, e, f)\<in>set c.
               \<forall>x\<in>{?bgrt<..y1}. d * x\<^sup>2 + e * x + f \<le> 0)" 
          proof clarsimp 
            fix t1 u1 v1 x1
            assume ins: "(t1, u1, v1) \<in> set c"
            assume x1gt: " sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < x1"
            assume x1lt: "x1 \<le> y1"
            have x1inbtw: "x1 > ?srl ! k \<and> x1 < ?srl ! (k+1)"
              using x1gt x1lt y1inbtw
              by (smt One_nat_def cases_gt k_prop) 
            have xsn: "sign_num (t1 * x^2 + u1 * x + v1 ) = -1 \<or> sign_num (t1 * x^2 + u1 * x + v1 ) = 0" using ins x_prop unfolding sign_num_def
              by auto
            have "sign_num (t1 * x1\<^sup>2 + u1 * x1 + v1 ) = sign_num (t1 * x^2 + u1 * x + v1 ) " 
              using ins x1inbtw samesign
              by blast 
            then show "t1 * x1\<^sup>2 + u1 * x1 + v1 \<le> 0" using xsn unfolding sign_num_def
              by (metis (no_types, hide_lams) equal_neg_zero less_eq_real_def linorder_not_less zero_neq_one) 
          qed
          have allpropcvar: "(\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0)" 
          proof clarsimp 
            fix t1 u1 v1
            assume "(t1, u1, v1) \<in> set c"
            then have "\<forall>x\<in>{?bgrt<..y1}. t1 * x\<^sup>2 + u1 * x + v1 \<le> 0"
              using allpropc 
              by force 
            then show " \<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k.
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 \<le> 0" 
              using y1inbtw by blast 
          qed
          have allpropd: "(\<forall>(d, e, f)\<in>set d.
              \<forall>x\<in>{?bgrt<..y1}. d * x\<^sup>2 + e * x + f \<noteq> 0)" 
          proof clarsimp 
            fix t1 u1 v1 x1
            assume ins: "(t1, u1, v1) \<in> set d"
            assume contrad:"t1 * x1\<^sup>2 + u1 * x1 + v1 = 0"
            assume x1gt: " sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k < x1"
            assume x1lt: "x1 \<le> y1"
            have x1inbtw: "x1 > ?srl ! k \<and> x1 < ?srl ! (k+1)"
              using x1gt x1lt y1inbtw
              by (smt One_nat_def cases_gt k_prop) 
            have xsn: "sign_num (t1 * x^2 + u1 * x + v1 ) = -1 \<or> sign_num (t1 * x^2 + u1 * x + v1 ) = 1" using ins x_prop unfolding sign_num_def
              by auto
            have "sign_num (t1 * x1\<^sup>2 + u1 * x1 + v1 ) = sign_num (t1 * x^2 + u1 * x + v1 ) " 
              using ins x1inbtw samesign
              by blast
            then have "t1 * x1\<^sup>2 + u1 * x1 + v1 \<noteq> 0" using xsn unfolding sign_num_def 
              by auto
            then show "False" using contrad by auto
          qed
          have allpropdvar: "(\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)" 
          proof clarsimp 
            fix t1 u1 v1
            assume "(t1, u1, v1) \<in> set d"
            then have "\<forall>x\<in>{?bgrt<..y1}. t1 * x\<^sup>2 + u1 * x + v1 \<noteq> 0"
              using allpropd
              by force 
            then show " \<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k.
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 \<noteq> 0" 
              using y1inbtw by blast 
          qed
          have "\<forall>x. (\<forall>(d, e, f)\<in>set a.
             d * x\<^sup>2 + e * x + f = 0)" using alleqsetvar
            by auto
          then have ast: "(\<forall>(d, e, f)\<in>set a.
             \<forall>x\<in>{?bgrt<..(?bgrt + 1)}. d * x\<^sup>2 + e * x + f = 0)"
            by auto
          have allpropavar: "(\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0)"
          proof clarsimp 
            fix t1 u1 v1 
            assume "(t1, u1, v1) \<in> set a"
            then have "\<forall>x\<in>{?bgrt<..(?bgrt + 1)}. t1 * x\<^sup>2 + u1 * x + v1 = 0 "
              using ast by auto 
            then show "\<exists>y'>sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k.
          \<forall>x\<in>{sorted_nonzero_root_list_set (set b \<union> set c \<union> set d) ! k<..y'}.
             t1 * x\<^sup>2 + u1 * x + v1 = 0" 
              using less_add_one by blast 
          qed

          have quadsetb: "((t, u, v) \<in> set b \<and> t\<noteq> 0) \<Longrightarrow> False"
          proof - 
            assume asm: "(t, u, v) \<in> set b \<and> t\<noteq> 0"
            have bgrt1: "(?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
            proof - 
              assume bgrtis: "?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
              have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
                by blast           
              have "((t, u, v)\<in>set b \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
                using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
                by linarith
              then show "False" using f6 bgrtis 
                by auto
            qed
            have bgrt2: "(?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
            proof -
              assume bgrtis: "?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
              have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
                by blast
              have "((t, u, v)\<in>set b \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
                using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
                by linarith
              then show "False" using f7 bgrtis 
                by auto
            qed 
            show "False" using tnonz bgrt1 bgrt2 asm 
              by auto
          qed
          have linsetb: "((t, u, v) \<in> set b \<and> (t = 0 \<and> u \<noteq> 0)) \<Longrightarrow> False"
          proof - 
            assume asm: "(t, u, v) \<in> set b \<and> (t = 0 \<and> u \<noteq> 0)"
            then have bgrtis: "?bgrt = (- v / u)"
              using unonz
              by blast 
            have "((t, u, v)\<in>set b \<and> (t = 0 \<and> u \<noteq> 0) \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using bgrtis f5  
              by auto
          qed
          have insetb: "((t, u, v) \<in> set b \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<Longrightarrow> False"
            using quadsetb linsetb by auto
          have quadsetc: "(t, u, v) \<in> set c \<and> t\<noteq> 0 \<Longrightarrow> False"
          proof - 
            assume asm: "(t, u, v) \<in> set c \<and> t\<noteq> 0"
            have bgrt1: "(?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
            proof - 
              assume bgrtis: "?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
              have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
                by blast 
              have "((t, u, v)\<in>set c \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
                using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
                by linarith
              then show "False" using f13a bgrtis 
                by auto
            qed
            have bgrt2: "(?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
            proof -
              assume bgrtis: "?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
              have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
                by blast
              have "((t, u, v)\<in>set c \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
                using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
                by linarith
              then show "False" using f9a bgrtis 
                by auto
            qed 
            show "False" using tnonz bgrt1 bgrt2 asm 
              by auto
          qed
          have linsetc: "(t, u, v) \<in> set c \<and> (t = 0 \<and> u \<noteq> 0) \<Longrightarrow> False"
          proof - 
            assume asm: "(t, u, v) \<in> set c \<and> (t = 0 \<and> u \<noteq> 0)"
            then have bgrtis: "?bgrt = (- v / u)"
              using unonz
              by blast 
            have "((t, u, v)\<in>set c \<and> (t = 0 \<and> u \<noteq> 0) \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using bgrtis f8a  
              by auto
          qed
          have insetc: "((t, u, v) \<in> set c \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<Longrightarrow> False"
            using quadsetc linsetc by auto
          have quadsetd: "(t, u, v) \<in> set d \<and> t\<noteq> 0 \<Longrightarrow> False"
          proof - 
            assume asm: "(t, u, v) \<in> set d \<and> t\<noteq> 0"
            have bgrt1: "(?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
            proof - 
              assume bgrtis: "?bgrt = (- u + 1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
              have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
                by blast
              have "((t, u, v)\<in>set d \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
                using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
                by linarith
              then show "False" using f11 bgrtis 
                by auto
            qed
            have bgrt2: "(?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)) \<Longrightarrow> False "
            proof -
              assume bgrtis: "?bgrt = (- u + -1 * sqrt (u^2 - 4 * t * v)) / (2 * t)"
              have discrim_prop: "-1*u^2 + 4 * t * v \<le> 0" using asm tnonz
                by blast
              have "((t, u, v)\<in>set d \<and> t \<noteq> 0 \<and> - 1*u^2 + 4 * t * v \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
                using asm discrim_prop allpropavar allpropbvar allpropcvar allpropdvar
                by linarith
              then show "False" using f12 bgrtis 
                by auto
            qed 
            show "False" using tnonz bgrt1 bgrt2 asm 
              by auto
          qed
          have linsetd: "(t, u, v) \<in> set d \<and> (t = 0 \<and> u \<noteq> 0) \<Longrightarrow> False"
          proof - 
            assume asm: "(t, u, v) \<in> set d \<and> (t = 0 \<and> u \<noteq> 0)"
            then have bgrtis: "?bgrt = (- v / u)"
              using unonz
              by blast 
            have "((t, u, v)\<in>set d \<and> (t = 0 \<and> u \<noteq> 0) \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>?bgrt. \<forall>x\<in>{?bgrt<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)))"
              using asm allpropavar allpropbvar allpropcvar allpropdvar
              by linarith
            then show "False" using bgrtis f10
              by auto
          qed
          have insetd: "((t, u, v) \<in> set d \<and> (t \<noteq> 0 \<or> u \<noteq> 0) \<and> (t * ?bgrt\<^sup>2 + u * ?bgrt + v = 0)) \<Longrightarrow> False"
            using quadsetd linsetd by auto
          then show "False" using insetb insetc insetd tuvprop 
            by auto
        qed
        show "False" using cases cases_btw cases_mem cases_lt cases_gt 
          by auto
      qed
      show "False" using asm len1 lengtone
        by linarith 
    qed
    show "False" using lenzero lengt0
      by linarith 
  qed
  then show ?thesis
    by blast  
qed


lemma qe_forwards: 
  assumes "(\<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
  shows "((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) \<or>
     (\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0))) \<or>
     (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))) \<or>
     (\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0))) \<or>
     (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))))" 
    (* using eq_qe_1 les_qe_1 *)
proof -
  let ?e2 = "(((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) 
     \<or>
     (\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)         
          \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))) 
    \<or>
     (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))) 
    \<or>
     (\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))) 
      \<or>
     (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))))"
  let ?f10orf11orf12 = "(\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f8orf9 = "(\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))"
  let ?f5orf6orf7 = "(\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f2orf3orf4 = "(\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)         
          \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))"
  let ?e1 = "(\<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
  let ?f1 = "((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0))"
  let ?f2 = "(\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
  let ?f3 = "(\<exists>(a', b', c')\<in>set a. a' \<noteq> 0 \<and> - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))"
  let ?f4 = "(\<exists>(a', b', c')\<in>set a. a' \<noteq> 0 \<and> - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
 (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)) "
  let ?f5 = "(\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  let ?f6 = "(\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f7 = "(\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  let ?f8 = "(\<exists>(a', b', c')\<in>set c. (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
  let ?f13 = "(\<exists>(a', b', c')\<in>set c.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))"
  let ?f9 = "(\<exists>(a', b', c')\<in>set c.  a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))"
  let ?f10 = "(\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  let ?f11 = "(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f12 = "(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  have h1a: "(?f1 \<or> ?f2orf3orf4 \<or> ?f5orf6orf7 \<or> ?f8orf9 \<or> ?f10orf11orf12) \<longrightarrow> ?e2"
    by auto
  have h2: "(?f2 \<or> ?f3 \<or> ?f4) \<longrightarrow> ?f2orf3orf4" by auto
  then have h1b: "(?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5orf6orf7 \<or> ?f8orf9 \<or> ?f10orf11orf12) \<longrightarrow> ?e2"
    using h1a by auto
  have h3: "(?f5 \<or> ?f6 \<or> ?f7) \<longrightarrow> ?f5orf6orf7" by auto
  then have h1c: "(?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8orf9 \<or> ?f10orf11orf12) \<longrightarrow> ?e2"
    using h1b by smt 
  have h4: "(?f8 \<or> ?f9 \<or> ?f13) \<longrightarrow> ?f8orf9" by auto
  then have h1d: "(?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8 \<or> ?f9 \<or> ?f13 \<or> ?f10orf11orf12) \<longrightarrow> ?e2"
    using h1c
    by smt 
  have h5: "(?f10 \<or> ?f11 \<or> ?f12) \<longrightarrow> ?f10orf11orf12" 
    by auto
  then have bigor: "(?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8 \<or> ?f13 \<or> ?f9 \<or> ?f10 \<or> ?f11 \<or> ?f12)
    \<longrightarrow> ?e2 "
    using h1d  by smt 
  then have bigor_var: "\<not>?e2 \<longrightarrow> \<not>(?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8 \<or> ?f13 \<or> ?f9 \<or> ?f10 \<or> ?f11 \<or> ?f12)
   " using contrapos_nn
    by smt 
  have not_eq: "\<not>(?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8 \<or> ?f13 \<or> ?f9 \<or> ?f10 \<or> ?f11 \<or> ?f12) 
=(\<not>?f1 \<and> \<not>?f2  \<and> \<not>?f3  \<and> \<not>?f4  \<and> \<not>?f5 \<and> \<not>?f6 \<and> \<not>?f7 \<and> \<not>?f8 \<and> \<not>?f13 \<and> \<not>?f9 \<and> \<not>?f10 \<and> \<not>?f11 \<and> \<not>?f12) "
    by linarith
  obtain x where x_prop: "(\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)" using assms by auto
  have "(\<not>?f1 \<and> \<not>?f2  \<and> \<not>?f3  \<and> \<not>?f4  \<and> \<not>?f5 \<and> \<not>?f6 \<and> \<not>?f7 \<and> \<not>?f8 \<and> \<not>?f13 \<and> \<not>?f9 \<and> \<not>?f10 \<and> \<not>?f11 \<and> \<not>?f12) \<Longrightarrow> False"
  proof - 
    assume big_not: " \<not> ((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
        (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set a.
           (a' = 0 \<and> b' \<noteq> 0) \<and>
           (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set a.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set a.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set b.
           (a' = 0 \<and> b' \<noteq> 0) \<and>
           (\<forall>(d, e, f)\<in>set a. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set b.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set b.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set c.
           (a' = 0 \<and> b' \<noteq> 0) \<and>
           (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set c.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f =
               0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f
               < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f
               \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq>
               0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set c.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f =
               0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f
               < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f
               \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq>
               0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set d.
           (a' = 0 \<and> b' \<noteq> 0) \<and>
           (\<forall>(d, e, f)\<in>set a. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set d.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<noteq> 0)) \<and>
    \<not> (\<exists>(a', b', c')\<in>set d.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                  \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                     d * x\<^sup>2 + e * x + f \<noteq> 0))"
    have c1: "(\<exists> (d, e, f) \<in> set a. d \<noteq> 0 \<and> - e\<^sup>2 + 4 * d * f \<le> 0) \<Longrightarrow> False"
    proof - 
      assume "(\<exists> (d, e, f) \<in> set a. d \<noteq> 0 \<and> - e\<^sup>2 + 4 * d * f \<le> 0)"
      then obtain a' b' c' where abc_prop:  "(a', b', c') \<in> set a \<and> a' \<noteq> 0 \<and> - b'\<^sup>2 + 4 * a' * c' \<le> 0"
        by auto
      then have "a'*x^2 + b'*x + c' = 0" using x_prop by auto
      then have xis: "x = (- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a') \<or> x = (- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a') " 
        using abc_prop discriminant_nonneg[of a' b' c'] unfolding discrim_def
        by auto 
      then have "((\<forall>(d, e, f)\<in>set a.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq> 0)) \<or>
        ((\<forall>(d, e, f)\<in>set a.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq> 0))"
        using x_prop by auto
      then have "(\<exists>(a', b', c')\<in>set a.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq> 0)) \<or>
        (\<exists>(a', b', c')\<in>set a.
           a' \<noteq> 0 \<and>
           - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
           (\<forall>(d, e, f)\<in>set a.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d.
               d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
               e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
               f \<noteq> 0))" using abc_prop xis by auto
      then show "False"
        using big_not by auto
    qed
    have c2: "(\<exists> (d, e, f) \<in> set a. d = 0 \<and> e \<noteq> 0) \<Longrightarrow> False"
    proof - 
      assume "(\<exists> (d, e, f) \<in> set a. d = 0 \<and> e \<noteq> 0)"
      then obtain a' b' c' where abc_prop: "(a', b', c') \<in> set a \<and> a' = 0 \<and> b' \<noteq> 0" by auto 
      then have "a'*x^2 + b'*x + c' = 0" using x_prop by auto
      then have "b'*x + c' = 0" using abc_prop by auto
      then have xis: "x = - c' / b'" using abc_prop
        by (smt divide_non_zero)
      then have "(\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)" 
        using x_prop by auto 
      then have "(\<exists>(a', b', c')\<in>set a.
           (a' = 0 \<and> b' \<noteq> 0) \<and>
           (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
           (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
           (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
           (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
        using abc_prop xis by auto
      then show "False"
        using big_not by auto 
    qed
    have c3: "(\<forall> (d, e, f) \<in> set a. d = 0 \<and> e = 0 \<and> f = 0) \<Longrightarrow> False"
    proof - 
      assume "(\<forall> (d, e, f) \<in> set a. d = 0 \<and> e = 0 \<and> f = 0)"
      then have equalset: "\<forall>x. (\<forall>(d, e, f)\<in>set a. d * x^2 + e * x + f = 0)"
        using case_prodE by auto
      have "\<not>?f5 \<and> \<not>?f6 \<and> \<not>?f7 \<and> \<not>?f8 \<and> \<not>?f13 \<and> \<not>?f9 \<and> \<not>?f10 \<and> \<not>?f11 \<and> \<not>?f12"
        using big_not by auto
      then have "\<not>(\<exists>x. (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
        using equalset big_not qe_forwards_helper[of a b c d] by auto
      then show "False"
        using x_prop by auto
    qed
    have eo: "(\<exists> (d, e, f) \<in> set a. d \<noteq> 0 \<and> - e\<^sup>2 + 4 * d * f \<le> 0) \<or> (\<exists> (d, e, f) \<in> set a. d = 0 \<and> e \<noteq> 0) \<or> (\<forall> (d, e, f) \<in> set a. d = 0 \<and> e = 0 \<and> f = 0)"
    proof - 
      have  "(\<forall> (d, e, f) \<in> set a. (d \<noteq> 0 \<longrightarrow>  - e\<^sup>2 + 4 * d * f \<le> 0))"
      proof clarsimp 
        fix d e f
        assume in_set: " (d, e, f) \<in> set a"
        assume dnonz: "d \<noteq> 0"
        have "d*x^2 + e*x + f = 0" using in_set x_prop by auto 
        then show " 4 * d * f \<le> e\<^sup>2"
          using dnonz discriminant_negative[of d e f] unfolding discrim_def
          by fastforce 
      qed
      then have discrim_prop: "\<not>(\<exists> (d, e, f) \<in> set a. d \<noteq> 0 \<and> - e\<^sup>2 + 4 * d * f \<le> 0) \<Longrightarrow> \<not>(\<exists> (d, e, f) \<in> set a. d \<noteq> 0)"
        by auto
      have "\<not>(\<exists> (d, e, f) \<in> set a. d \<noteq> 0) \<and> \<not>(\<exists> (d, e, f) \<in> set a. d = 0 \<and> e \<noteq> 0) \<Longrightarrow> (\<forall> (d, e, f) \<in> set a. d = 0 \<and> e = 0 \<and> f = 0)"
      proof - 
        assume ne: "\<not>(\<exists> (d, e, f) \<in> set a. d \<noteq> 0) \<and> \<not>(\<exists> (d, e, f) \<in> set a. d = 0 \<and> e \<noteq> 0)"
        show "(\<forall> (d, e, f) \<in> set a. d = 0 \<and> e = 0 \<and> f = 0)"
        proof clarsimp 
          fix d e f 
          assume in_set: "(d, e, f) \<in>set a"
          then have xzer: "d*x^2 + e*x + f = 0" using x_prop by auto
          have dzer: "d = 0" using ne in_set by auto
          have ezer: "e = 0" using ne in_set by auto
          show "d = 0 \<and> e = 0 \<and> f = 0" using xzer dzer ezer by auto 
        qed
      qed
      then show ?thesis using discrim_prop by auto
    qed
    show "False" using c1 c2 c3 eo by auto 
  qed
  then have " \<not>?e2 \<Longrightarrow> False" using bigor_var not_eq
    by presburger (* Takes a second *) 
  then have " \<not>?e2 \<longrightarrow> False" using impI[of "\<not>?e2" "False"]
    by blast 
  then show ?thesis 
    by auto
qed

subsubsection "Some Cases and Misc"
lemma quadratic_linear :
  assumes "b\<noteq>0"
  assumes "a \<noteq> 0"
  assumes "4 * a * ba \<le> aa\<^sup>2"
  assumes "b * (sqrt (aa\<^sup>2 - 4 * a * ba) - aa) / (2 * a) + c = 0"
  assumes "\<forall>x\<in>set eq.
          case x of
          (d, e, f) \<Rightarrow>
            d * ((sqrt (aa\<^sup>2 - 4 * a * ba) - aa) / (2 * a))\<^sup>2 +
            e * (sqrt (aa\<^sup>2 - 4 * a * ba) - aa) / (2 * a) +
            f =
            0"
  assumes "(aaa, aaaa, baa) \<in> set eq"
  shows "aaa * (c / b)\<^sup>2 - aaaa * c / b + baa = 0"
proof-
  have h:  "-(c/b) = (sqrt (aa\<^sup>2 - 4 * a * ba) - aa) / (2 * a)"
    using assms
    by (smt divide_minus_left nonzero_mult_div_cancel_left times_divide_eq_right)
  have h1 : "\<forall>x\<in>set eq. case x of (d, e, f) \<Rightarrow> d * (c / b)\<^sup>2 + e * - (c / b) + f = 0"
    using assms(5) unfolding h[symmetric] Fields.division_ring_class.times_divide_eq_right[symmetric]
      Power.ring_1_class.power2_minus .
  show ?thesis  
    using bspec[OF h1 assms(6)] by simp
qed

lemma quadratic_linear1:  
  assumes "b\<noteq>0"
  assumes "a \<noteq> 0"
  assumes "4 * a * ba \<le> aa\<^sup>2"
  assumes "(b::real) * (sqrt ((aa::real)\<^sup>2 - 4 * (a::real) * (ba::real)) - (aa::real)) / (2 * a) + (c::real) = 0"
  assumes "
       (\<forall>x\<in>set (les::(real*real*real)list).
          case x of
          (d, e, f) \<Rightarrow>
            d * ((sqrt (aa\<^sup>2 - 4 * a * ba) - aa) / (2 * a))\<^sup>2 +
            e * (sqrt (aa\<^sup>2 - 4 * a * ba) - aa) / (2 * a) +
            f
            < 0)"
  assumes "(aaa, aaaa, baa) \<in> set les"
  shows "aaa * (c / b)\<^sup>2 - aaaa * c / b + baa < 0"
proof-
  have h:  "-(c/b) = (sqrt (aa\<^sup>2 - 4 * a * ba) - aa) / (2 * a)"
    using assms
    by (smt divide_minus_left nonzero_mult_div_cancel_left times_divide_eq_right)
  have h1 : "\<forall>x\<in>set les. case x of (d, e, f) \<Rightarrow> d * (c / b)\<^sup>2 + e * - (c / b) + f < 0"
    using assms(5) unfolding h[symmetric] Fields.division_ring_class.times_divide_eq_right[symmetric]
      Power.ring_1_class.power2_minus .
  show ?thesis  
    using bspec[OF h1 assms(6)] by simp
qed

lemma quadratic_linear2 :
  assumes "b\<noteq>0"
  assumes "a \<noteq> 0"
  assumes "4 * a * ba \<le> aa\<^sup>2"
  assumes "b * (- aa -sqrt (aa\<^sup>2 - 4 * a * ba)) / (2 * a) + c = 0"
  assumes "\<forall>x\<in>set eq.
          case x of
          (d, e, f) \<Rightarrow>
            d * ((- aa -sqrt (aa\<^sup>2 - 4 * a * ba)) / (2 * a))\<^sup>2 +
            e * (- aa -sqrt (aa\<^sup>2 - 4 * a * ba)) / (2 * a) +
            f =
            0"
  assumes "(aaa, aaaa, baa) \<in> set eq"
  shows "aaa * (c / b)\<^sup>2 - aaaa * c / b + baa = 0"
proof-
  have h:  "-((c::real)/(b::real)) = (- (aa::real) -sqrt (aa\<^sup>2 - 4 * (a::real) * (ba::real))) / (2 * a)"
    using assms
    by (smt divide_minus_left nonzero_mult_div_cancel_left times_divide_eq_right)
  have h1 : "\<forall>x\<in>set eq. case x of (d, e, f) \<Rightarrow> d * (c / b)\<^sup>2 + e * - (c / b) + f = 0"
    using assms(5) unfolding h[symmetric] Fields.division_ring_class.times_divide_eq_right[symmetric]
      Power.ring_1_class.power2_minus .
  show ?thesis  
    using bspec[OF h1 assms(6)] by simp
qed

lemma quadratic_linear3:  
  assumes "b\<noteq>0"
  assumes "a \<noteq> 0"
  assumes "4 * a * ba \<le> aa\<^sup>2"
  assumes "(b::real) * (- (aa::real)- sqrt ((aa::real)\<^sup>2 - 4 * (a::real) * (ba::real)) ) / (2 * a) + (c::real) = 0"
  assumes "(\<forall>x\<in>set (les::(real*real*real)list).
          case x of
          (d, e, f) \<Rightarrow>
            d * ((- aa - sqrt (aa\<^sup>2 - 4 * a * ba)) / (2 * a))\<^sup>2 +
            e * (- aa - sqrt (aa\<^sup>2 - 4 * a * ba)) / (2 * a) +
            f
            < 0)"
  assumes "(aaa, aaaa, baa) \<in> set les"
  shows "aaa * (c / b)\<^sup>2 - aaaa * c / b + baa < 0"
proof-
  have h:  "-((c::real)/(b::real)) = (- (aa::real) -sqrt (aa\<^sup>2 - 4 * (a::real) * (ba::real))) / (2 * a)"
    using assms
    by (smt divide_minus_left nonzero_mult_div_cancel_left times_divide_eq_right)
  have h1 : "\<forall>x\<in>set les. case x of (d, e, f) \<Rightarrow> d * (c / b)\<^sup>2 + e * - (c / b) + f < 0"
    using assms(5) unfolding h[symmetric] Fields.division_ring_class.times_divide_eq_right[symmetric]
      Power.ring_1_class.power2_minus .
  show ?thesis  
    using bspec[OF h1 assms(6)] by simp
qed


lemma h1b_helper_les: 
  "(\<forall>((a::real), (b::real), (c::real))\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))"
proof - 
  show "(\<forall>(a, b, c)\<in>set les. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set les. a * x\<^sup>2 + b * x + c < 0))" 
  proof (induct les)
    case Nil
    then show ?case
      by auto
  next
    case (Cons q les) 
    have ind: " \<forall>a\<in>set (q # les). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0"
      using Cons.prems
      by auto
    then have "case q of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0 "
      by simp      
    then obtain y2 where y2_prop: "case q of (a, ba, c) \<Rightarrow>  (\<forall>y<y2. a * y\<^sup>2 + ba * y + c < 0)"
      by auto
    have "\<forall>a\<in>set les. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0"
      using ind by simp
    then have " \<exists>y. \<forall>x<y. \<forall>a\<in>set les. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c < 0"
      using Cons.hyps by blast 
    then obtain y1 where y1_prop: "\<forall>x<y1. \<forall>a\<in>set les. case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c < 0"
      by blast
    let ?y = "min y1 y2"
    have "\<forall>x < ?y.  (\<forall>a\<in>set (q #les). case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c < 0)"
      using y1_prop y2_prop 
      by fastforce 
    then show ?case
      by blast 
  qed
qed

lemma h1b_helper_leq: 
  "(\<forall>((a::real), (b::real), (c::real))\<in>set leq. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set leq. a * x\<^sup>2 + b * x + c \<le> 0))"
proof - 
  show "(\<forall>(a, b, c)\<in>set leq. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set leq. a * x\<^sup>2 + b * x + c \<le> 0))" 
  proof (induct leq)
    case Nil
    then show ?case
      by auto
  next
    case (Cons q leq) 
    have ind: " \<forall>a\<in>set (q # leq). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0"
      using Cons.prems
      by auto
    then have "case q of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0 "
      by simp      
    then obtain y2 where y2_prop: "case q of (a, ba, c) \<Rightarrow>  (\<forall>y<y2. a * y\<^sup>2 + ba * y + c \<le> 0)"
      by auto
    have "\<forall>a\<in>set leq. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0"
      using ind by simp
    then have " \<exists>y. \<forall>x<y. \<forall>a\<in>set leq. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<le> 0"
      using Cons.hyps by blast 
    then obtain y1 where y1_prop: "\<forall>x<y1. \<forall>a\<in>set leq. case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c \<le> 0"
      by blast
    let ?y = "min y1 y2"
    have "\<forall>x < ?y.  (\<forall>a\<in>set (q #leq). case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c \<le> 0)"
      using y1_prop y2_prop 
      by fastforce 
    then show ?case
      by blast 
  qed
qed

lemma h1b_helper_neq: 
  "(\<forall>((a::real), (b::real), (c::real))\<in>set neq. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set neq. a * x\<^sup>2 + b * x + c \<noteq> 0))"
proof - 
  show "(\<forall>(a, b, c)\<in>set neq. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) \<Longrightarrow> (\<exists>y.\<forall>x<y. (\<forall>(a, b, c)\<in>set neq. a * x\<^sup>2 + b * x + c \<noteq> 0))" 
  proof (induct neq)
    case Nil
    then show ?case
      by auto
  next
    case (Cons q neq) 
    have ind: " \<forall>a\<in>set (q # neq). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0"
      using Cons.prems
      by auto
    then have "case q of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0 "
      by simp      
    then obtain y2 where y2_prop: "case q of (a, ba, c) \<Rightarrow>  (\<forall>y<y2. a * y\<^sup>2 + ba * y + c \<noteq> 0)"
      by auto
    have "\<forall>a\<in>set neq. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0"
      using ind by simp
    then have " \<exists>y. \<forall>x<y. \<forall>a\<in>set neq. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<noteq> 0"
      using Cons.hyps by blast 
    then obtain y1 where y1_prop: "\<forall>x<y1. \<forall>a\<in>set neq. case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c \<noteq> 0"
      by blast
    let ?y = "min y1 y2"
    have "\<forall>x < ?y.  (\<forall>a\<in>set (q #neq). case a of (a, ba, c) \<Rightarrow> a * x^2 + ba * x + c \<noteq> 0)"
      using y1_prop y2_prop 
      by fastforce 
    then show ?case
      by blast 
  qed
qed


lemma min_lem: 
  fixes r::"real"
  assumes a1: "(\<exists>y'>r. (\<forall>((d::real), (e::real), (f::real))\<in>set b. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f < 0))" 
  assumes a2: "(\<exists>y'>r. (\<forall>((d::real), (e::real), (f::real))\<in>set c. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<le> 0))"
  assumes a3: "(\<exists>y'>r. (\<forall>((d::real), (e::real), (f::real))\<in>set d. \<forall>x\<in>{r<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
proof - 
  obtain y1 where y1_prop: "y1 > r \<and> (\<forall>(d, e, f)\<in>set b.  \<forall>x\<in>{r<..y1}. d * x\<^sup>2 + e * x + f < 0)"
    using a1 by auto
  obtain y2 where y2_prop: "y2 > r \<and> (\<forall>(d, e, f)\<in>set c.  \<forall>x\<in>{r<..y2}. d * x\<^sup>2 + e * x + f \<le> 0)"
    using a2 by auto
  obtain y3 where y3_prop: "y3 > r \<and> (\<forall>(d, e, f)\<in>set d.  \<forall>x\<in>{r<..y3}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
    using a3 by auto
  let ?y = "(min (min y1 y2) y3)"
  have "?y > r" using y1_prop y2_prop y3_prop by auto
  then have "\<exists>x. x > r \<and> x < ?y" using dense[of r ?y] 
    by auto
  then obtain x where x_prop: "x > r \<and> x < ?y" by auto
  have bp: "(\<forall>(a, b, c)\<in>set b. a *x\<^sup>2 + b * x + c < 0)"  
    using x_prop y1_prop by auto 
  have cp: "(\<forall>(a, b, c)\<in>set c. a * x^2 + b * x + c \<le> 0)"  
    using x_prop y2_prop by auto 
  have dp: "(\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)"  
    using x_prop y3_prop by auto 
  then have  "(\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)"
    using  bp cp dp by auto
  then show ?thesis by auto
qed 

lemma qe_infinitesimals_helper:
  fixes k::"real"
  assumes asm: "(\<forall>(d, e, f)\<in>set a. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. \<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
  shows "(\<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
proof -
  have "\<forall>(d, e, f)\<in>set a. d = 0 \<and> e = 0 \<and> f = 0" 
  proof clarsimp 
    fix d e f
    assume "(d, e, f) \<in> set a"
    then have "\<exists>y'>k. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f = 0"
      using asm by auto
    then obtain y' where y_prop: "y'>k \<and> (\<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f = 0)"
      by auto
    then show "d = 0 \<and> e = 0 \<and> f = 0" using continuity_lem_eq0[of "k" "y'" d e f]
      by auto
  qed
  then have eqprop: "\<forall>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) "
    by auto
  have lesprop: "(\<exists>y'>k. (\<forall>(d, e, f)\<in>set b. \<forall>x\<in>{k<..y'}. d * x\<^sup>2 + e * x + f < 0))" 
    using les_qe_inf_helper[of b "k"] asm 
    by blast 
  have leqprop: "(\<exists>y'>k. (\<forall>(d, e, f)\<in>set c. \<forall>x\<in>{(k)<..y'}. d * x\<^sup>2 + e * x + f \<le> 0))" 
    using leq_qe_inf_helper[of c "k"] asm 
    by blast 
  have neqprop: "(\<exists>y'>(k). (\<forall>(d, e, f)\<in>set d. \<forall>x\<in>{(k)<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))" 
    using neq_qe_inf_helper[of d "k"] asm 
    by blast  
  then have "(\<exists>x. (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)) " 
    using lesprop leqprop neqprop min_lem[of "k" b c d]
    by auto
  then show ?thesis
    using eqprop by auto 
qed

subsubsection "The qe\\_backwards lemma"
lemma qe_backwards: 
  assumes "(((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) 
     \<or>
     (\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)        
          \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))) 
    \<or>
     (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))) 
    \<or>
     (\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))) 
      \<or>
     (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))))"
  shows " (\<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))" 
proof - 
  let ?e2 = "(((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) 
     \<or>
     (\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)         
          \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))) 
    \<or>
     (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))) 
    \<or>
     (\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))) 
      \<or>
     (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))))"
  let ?f10orf11orf12 = "(\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f8orf9 = "(\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))"
  let ?f5orf6orf7 = "(\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) 
      \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f2orf3orf4 = "(\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) 
        \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)         
          \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))"
  let ?e1 = "(\<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
  let ?f1 = "((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0))"
  let ?f2 = "(\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
  let ?f3 = "(\<exists>(a', b', c')\<in>set a. a' \<noteq> 0 \<and> - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))"
  let ?f4 = "(\<exists>(a', b', c')\<in>set a. a' \<noteq> 0 \<and> - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
 (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)) "
  let ?f5 = "(\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  let ?f6 = "(\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f7 = "(\<exists>(a', b', c')\<in>set b. a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  let ?f8 = "(\<exists>(a', b', c')\<in>set c. (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0))"
  let ?f13 = "(\<exists>(a', b', c')\<in>set c.
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0)))"
  let ?f9 = "(\<exists>(a', b', c')\<in>set c.  a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
        (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq> 0))"
  let ?f10 = "(\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0))"
  let ?f11 = "(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"
  let ?f12 = "(\<exists>(a', b', c')\<in>set d.
          a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))"
  have h1a: "?e2 \<longrightarrow> (?f1 \<or> ?f2orf3orf4 \<or> ?f5orf6orf7 \<or> ?f8orf9 \<or> ?f10orf11orf12)"
    by auto
  have h2: "?f2orf3orf4 \<longrightarrow> (?f2 \<or> ?f3 \<or> ?f4)" by auto
  then have h1b: "?e2 \<longrightarrow> (?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5orf6orf7 \<or> ?f8orf9 \<or> ?f10orf11orf12) "
    using h1a by auto
  have h3: "?f5orf6orf7 \<longrightarrow> (?f5 \<or> ?f6 \<or> ?f7)" by auto
  then have h1c: "?e2 \<longrightarrow> (?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8orf9 \<or> ?f10orf11orf12) "
    using h1b by smt 
  have h4: "?f8orf9 \<longrightarrow> (?f8 \<or> ?f9 \<or> ?f13)" by auto
  then have h1d: "?e2 \<longrightarrow> (?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8 \<or> ?f9 \<or> ?f13 \<or> ?f10orf11orf12) "
    using h1c
    by smt 
  have h5: "?f10orf11orf12 \<longrightarrow> (?f10 \<or> ?f11 \<or> ?f12)" 
    by auto
  then have bigor: "?e2 \<longrightarrow> (?f1 \<or> ?f2 \<or> ?f3 \<or> ?f4 \<or> ?f5 \<or> ?f6 \<or> ?f7 \<or> ?f8 \<or> ?f13 \<or> ?f9 \<or> ?f10 \<or> ?f11 \<or> ?f12) "
    using h1d  by smt 
  have "?f1 \<Longrightarrow> ?e1"
  proof - 
    assume asm: "(\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
    (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
    (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
    (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0)"
    then have eqprop: "\<forall>x. \<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0" by auto
    have "\<exists>y. \<forall>x<y. \<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0"
      using asm h1b_helper_les by auto
    then obtain y1 where y1_prop: "\<forall>x<y1. \<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0" by auto
    have "\<exists>y. \<forall>x<y. \<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0"
      using asm h1b_helper_leq by auto
    then obtain y2 where y2_prop: "\<forall>x<y2. \<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0" by auto
    have "\<exists>y. \<forall>x<y. \<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0"
      using asm h1b_helper_neq by auto
    then obtain y3 where y3_prop: "\<forall>x<y3. \<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0" by auto
    let ?y = "(min (min y1 y2) y3) - 1"
    have y_prop: "?y < y1 \<and> ?y < y2 \<and> ?y < y3"
      by auto
    have ap: "(\<forall>(a, b, c)\<in>set a. a * ?y\<^sup>2 + b * ?y + c = 0)" 
      using eqprop by auto
    have bp: "(\<forall>(a, b, c)\<in>set b. a * ?y\<^sup>2 + b * ?y + c < 0)"  
      using y_prop y1_prop by auto 
    have cp: "(\<forall>(a, b, c)\<in>set c. a * ?y\<^sup>2 + b * ?y + c \<le> 0)"  
      using y_prop y2_prop by auto 
    have dp: "(\<forall>(a, b, c)\<in>set d. a * ?y\<^sup>2 + b * ?y + c \<noteq> 0)"  
      using y_prop y3_prop by auto 
    then have  "(\<forall>(a, b, c)\<in>set a. a * ?y\<^sup>2 + b * ?y + c = 0) \<and>
        (\<forall>(a, b, c)\<in>set b. a * ?y\<^sup>2 + b * ?y + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. a * ?y\<^sup>2 + b * ?y + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. a * ?y\<^sup>2 + b * ?y + c \<noteq> 0)"
      using ap bp cp dp by auto
    then show ?thesis by auto
  qed
  then have h1: "?f1 \<longrightarrow> ?e1" 
    by auto
  have "?f2 \<Longrightarrow> ?e1" 
  proof - 
    assume " \<exists>(a', b', c')\<in>set a.
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set a \<and>
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)"
      by auto
    then have "\<exists>(x::real). x = -c'/b'" by auto
    then obtain x where x_prop: "x = - c' / b'" by auto
    then have "(\<forall>xa\<in>set a. case xa of (a, b, c) \<Rightarrow> a * x\<^sup>2 + b * x + c = 0) \<and>
        (\<forall>xa\<in>set b. case xa of (a, b, c) \<Rightarrow> a * x\<^sup>2 + b * x + c < 0) \<and>
        (\<forall>xa\<in>set c. case xa of (a, b, c) \<Rightarrow> a * x\<^sup>2 + b * x + c \<le> 0) \<and>
        (\<forall>xa\<in>set d. case xa of (a, b, c) \<Rightarrow> a * x\<^sup>2 + b * x + c \<noteq> 0)"
      using abc_prop by auto
    then show ?thesis by auto
  qed
  then have h2: "?f2 \<longrightarrow> ?e1" 
    by auto
  have "?f3 \<Longrightarrow> ?e1" 
  proof -
    assume "\<exists>(a', b', c')\<in>set a.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f  \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set a \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f  \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq> 0)" by auto
    then have "\<exists>(x::real). x = (- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then obtain x where x_prop: " x = (- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then have "(\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
        (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)" using abc_prop by auto
    then show ?thesis by auto
  qed
  then have h3: "?f3  \<longrightarrow> ?e1" 
    by auto
  have "?f4 \<Longrightarrow> ?e1" 
  proof -
    assume " \<exists>(a', b', c')\<in>set a.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set a \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq> 0)" by auto
    then have "\<exists>(x::real). x = (- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then obtain x where x_prop: " x = (- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then have "(\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
        (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)" using abc_prop by auto
    then show ?thesis by auto
  qed
  then have "?f4 \<longrightarrow> ?e1" by auto
  have "?f5 \<Longrightarrow> ?e1" 
  proof - 
    assume asm: "\<exists>(a', b', c')\<in>set b.
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set b \<and>
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
      by auto
    then show ?thesis using qe_infinitesimals_helper[of a "- c' / b'" b c d]
      by auto
  qed
  then have h5: "?f5 \<longrightarrow> ?e1" 
    by auto
  have "?f6 \<Longrightarrow> ?e1" 
  proof - 
    assume "\<exists>(a', b', c')\<in>set b.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set b \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)" by auto
    then show ?thesis using qe_infinitesimals_helper[of a "(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" b c d]
      by auto
  qed
  then have h6: "?f6  \<longrightarrow> ?e1" 
    by auto
  have "?f7 \<Longrightarrow> ?e1" 
  proof - 
    assume "\<exists>(a', b', c')\<in>set b.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set b \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)"
      by auto
    then show ?thesis using qe_infinitesimals_helper[of a "(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" b c d]
      by auto
  qed
  then have h7: "?f7 \<longrightarrow> ?e1"
    by auto
  have "?f8 \<Longrightarrow> ?e1"   
  proof -
    assume "\<exists>(a', b', c')\<in>set c.
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set c \<and>
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0)" by auto
    then have "\<exists>(x::real). x = (- c' / b')" by auto
    then obtain x where x_prop: " x = - c' / b'" by auto
    then have "(\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
        (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)" using abc_prop by auto
    then show ?thesis by auto
  qed
  then have h8: "?f8 \<longrightarrow> ?e1" by auto
  have "?f9 \<Longrightarrow> ?e1" 
  proof -
    assume "\<exists>(a', b', c')\<in>set c.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f =  0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set c \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f =  0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f  < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq>  0)" by auto
    then have "\<exists>(x::real). x = (- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then obtain x where x_prop: " x = (- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then have "(\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
        (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)" using abc_prop by auto
    then show ?thesis by auto
  qed
  then have h9:  "?f9 \<longrightarrow> ?e1" by auto
  have "?f10 \<Longrightarrow> ?e1"
  proof - 
    assume asm: "\<exists>(a', b', c')\<in>set d.
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set d \<and>
       (a' = 0 \<and> b' \<noteq> 0) \<and>
       (\<forall>(d, e, f)\<in>set a. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d. \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0)"
      by auto
    then show ?thesis using qe_infinitesimals_helper[of a "- c' / b'" b c d]
      by auto
  qed
  then have h10: "?f10 \<longrightarrow> ?e1" by auto
  have "?f11 \<Longrightarrow> ?e1"   
  proof - 
    assume "\<exists>(a', b', c')\<in>set d.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set d \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)" by auto
    then show ?thesis using qe_infinitesimals_helper[of a "(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" b c d]
      by auto
  qed
  then have h11: "?f11 \<longrightarrow> ?e1" by auto
  have "?f12 \<Longrightarrow> ?e1"  proof - 
    assume "\<exists>(a', b', c')\<in>set d.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set d \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
              \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                 d * x\<^sup>2 + e * x + f \<noteq> 0)"
      by auto
    then show ?thesis using qe_infinitesimals_helper[of a "(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" b c d]
      by auto
  qed
  then have h12: "?f12 \<longrightarrow> ?e1" by auto
  have "?f13 \<Longrightarrow> ?e1" proof -
    assume " \<exists>(a', b', c')\<in>set c.
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq> 0)"
    then obtain a' b' c' where abc_prop: "(a', b', c')\<in>set c \<and>
       a' \<noteq> 0 \<and>
       - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
       (\<forall>(d, e, f)\<in>set a.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f = 0) \<and>
       (\<forall>(d, e, f)\<in>set b.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f < 0) \<and>
       (\<forall>(d, e, f)\<in>set c.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<le> 0) \<and>
       (\<forall>(d, e, f)\<in>set d.
           d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
           e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
           f \<noteq> 0)" by auto
    then have "\<exists>(x::real). x = (- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then obtain x where x_prop: " x = (- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')" by auto
    then have "(\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
        (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
        (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
        (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)" using abc_prop by auto
    then show ?thesis by auto
  qed
  then have h13: "?f13 \<longrightarrow> ?e1" by auto
  show ?thesis using bigor h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    using assms
    by (smt \<open>\<exists>(a', b', c')\<in>set a. a' \<noteq> 0 \<and> - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and> (\<forall>(d, e, f)\<in>set a. d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 + e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) + f = 0) \<and> (\<forall>(d, e, f)\<in>set b. d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 + e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) + f < 0) \<and> (\<forall>(d, e, f)\<in>set c. d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 + e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) + f \<le> 0) \<and> (\<forall>(d, e, f)\<in>set d. d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 + e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) + f \<noteq> 0) \<Longrightarrow> \<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and> (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and> (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and> (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)\<close>) 
      (* by force *)
qed

subsection "General QE lemmas"

lemma qe: "(\<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0)) =
    ((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) \<or>
     (\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0))) \<or>
     (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))) \<or>
     (\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0))) \<or>
     (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))))" 
proof - 
  let ?e1 = "((\<forall>(a, b, c)\<in>set a. a = 0 \<and> b = 0 \<and> c = 0) \<and>
     (\<forall>(a, b, c)\<in>set b. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<and>
     (\<forall>(a, b, c)\<in>set c. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<and>
     (\<forall>(a, b, c)\<in>set d. \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<noteq> 0) \<or>
     (\<exists>(a', b', c')\<in>set a.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0))) \<or>
     (\<exists>(a', b', c')\<in>set b.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))) \<or>
     (\<exists>(a', b', c')\<in>set c.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d. d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f =
              0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f
              \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
              e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
              f \<noteq>
              0))) \<or>
     (\<exists>(a', b', c')\<in>set d.
         (a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set b.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set c.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set d.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
          (\<forall>(d, e, f)\<in>set a.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set b.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set c.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set d.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0))))" 
  let ?e2 = "(\<exists>x. (\<forall>(a, b, c)\<in>set a. a * x\<^sup>2 + b * x + c = 0) \<and>
         (\<forall>(a, b, c)\<in>set b. a * x\<^sup>2 + b * x + c < 0) \<and>
         (\<forall>(a, b, c)\<in>set c. a * x\<^sup>2 + b * x + c \<le> 0) \<and>
         (\<forall>(a, b, c)\<in>set d. a * x\<^sup>2 + b * x + c \<noteq> 0))"
  have h1: "?e1 \<longrightarrow> ?e2" using qe_backwards 
    by auto
  have h2: "?e2 \<longrightarrow> ?e1" using qe_forwards
    by auto
  have "(?e2 \<longrightarrow> ?e1) \<and> (?e1 \<longrightarrow> ?e2) " using h1 h2
    by force 
  then have  "?e2 \<longleftrightarrow> ?e1"
    using iff_conv_conj_imp[of ?e1 ?e2]
    by presburger
  then show ?thesis
    by auto
qed


fun eq_fun :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real*real*real) list \<Rightarrow> (real*real*real) list \<Rightarrow> (real*real*real) list \<Rightarrow> (real*real*real) list \<Rightarrow> bool" where
  "eq_fun a' b' c' eq les leq neq = ((a' = 0 \<and> b' \<noteq> 0) \<and>
          (\<forall>a\<in>set eq.
              case a of (d, e, f) \<Rightarrow> d * (- c' / b')\<^sup>2 + e * (- c' / b') + f = 0) \<and>
          (\<forall>a\<in>set les.
              case a of (d, e, f) \<Rightarrow> d * (- c' / b')\<^sup>2 + e * (- c' / b') + f < 0) \<and>
          (\<forall>a\<in>set leq.
              case a of (d, e, f) \<Rightarrow> d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<le> 0) \<and>
          (\<forall>a\<in>set neq.
              case a of (d, e, f) \<Rightarrow> d * (- c' / b')\<^sup>2 + e * (- c' / b') + f \<noteq> 0) \<or>
          a' \<noteq> 0 \<and>
          - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
          ((\<forall>a\<in>set eq.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f =
                 0) \<and>
           (\<forall>a\<in>set les.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f
                 < 0) \<and>
           (\<forall>a\<in>set leq.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f
                 \<le> 0) \<and>
           (\<forall>a\<in>set neq.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f \<noteq>
                 0) \<or>
           (\<forall>a\<in>set eq.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f =
                 0) \<and>
           (\<forall>a\<in>set les.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f
                 < 0) \<and>
           (\<forall>a\<in>set leq.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f
                 \<le> 0) \<and>
           (\<forall>a\<in>set neq.
               case a of
               (d, e, f) \<Rightarrow>
                 d * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a'))\<^sup>2 +
                 e * ((- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')) +
                 f \<noteq>
                 0)))"

fun les_fun :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real*real*real) list \<Rightarrow> (real*real*real) list \<Rightarrow> (real*real*real) list \<Rightarrow> (real*real*real) list \<Rightarrow> bool" where 
  "les_fun a' b' c' eq les leq neq = ((a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set eq.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f = 0) \<and>
         (\<forall>(d, e, f)\<in>set les.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f < 0) \<and>
         (\<forall>(d, e, f)\<in>set leq.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<le> 0) \<and>
         (\<forall>(d, e, f)\<in>set neq.
             \<exists>y'>- c' / b'. \<forall>x\<in>{- c' / b'<..y'}. d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set eq.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set leq.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set neq.
              \<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0) \<or>
          (\<forall>(d, e, f)\<in>set eq.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f = 0) \<and>
          (\<forall>(d, e, f)\<in>set les.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f < 0) \<and>
          (\<forall>(d, e, f)\<in>set leq.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<le> 0) \<and>
          (\<forall>(d, e, f)\<in>set neq.
              \<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
                 \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
                    d * x\<^sup>2 + e * x + f \<noteq> 0)))"

lemma general_qe' :
  (* Direct substitution F(x) *)
  assumes "F = (\<lambda>x. 
               (\<forall>(a,b,c)\<in>set eq . a*x\<^sup>2+b*x+c=0)\<and>
               (\<forall>(a,b,c)\<in>set les. a*x\<^sup>2+b*x+c<0)\<and>
               (\<forall>(a,b,c)\<in>set leq. a*x\<^sup>2+b*x+c\<le>0)\<and>
               (\<forall>(a,b,c)\<in>set neq. a*x\<^sup>2+b*x+c\<noteq>0))"
    (* Substitution of r+\<epsilon> into F *)
  assumes "F\<epsilon> = (\<lambda>r. 
         (\<forall>(a,b,c)\<in>set eq.  \<exists>y>r.\<forall>x\<in>{r<..y}. a*x\<^sup>2+b*x+c=0) \<and>
         (\<forall>(a,b,c)\<in>set les. \<exists>y>r.\<forall>x\<in>{r<..y}. a*x\<^sup>2+b*x+c<0) \<and>
         (\<forall>(a,b,c)\<in>set leq. \<exists>y>r.\<forall>x\<in>{r<..y}. a*x\<^sup>2+b*x+c\<le>0) \<and>
         (\<forall>(a,b,c)\<in>set neq. \<exists>y>r.\<forall>x\<in>{r<..y}. a*x\<^sup>2+b*x+c\<noteq>0)
        )"
    (* Substitution of -\<infinity> into F *)
  assumes "F\<^sub>i\<^sub>n\<^sub>f = (
     (\<forall>(a,b,c)\<in>set eq.  \<exists>x. \<forall>y<x. a*y\<^sup>2+b*y+c=0) \<and>
     (\<forall>(a,b,c)\<in>set les. \<exists>x. \<forall>y<x. a*y\<^sup>2+b*y+c<0) \<and>
     (\<forall>(a,b,c)\<in>set leq. \<exists>x. \<forall>y<x. a*y\<^sup>2+b*y+c\<le>0) \<and>
     (\<forall>(a,b,c)\<in>set neq. \<exists>x. \<forall>y<x. a*y\<^sup>2+b*y+c\<noteq>0)
    )"
    (* finds linear or quadratic roots of a polynomial *)
  assumes "roots = (\<lambda>(a,b,c).
     if a=0 \<and> b\<noteq>0 then {-c/b}::real set else
     if a\<noteq>0 \<and> b\<^sup>2-4*a*c\<ge>0 then {(-b+sqrt(b\<^sup>2-4*a*c))/(2*a)}\<union>{(-b-sqrt(b\<^sup>2-4*a*c))/(2*a)} else {})"
    (* all the root of each atom *)
  assumes "A = \<Union>(roots ` (set eq))"
  assumes "B = \<Union>(roots ` (set les))"
  assumes "C = \<Union>(roots ` (set leq))"
  assumes "D = \<Union>(roots ` (set neq))"
    (* Quantifier Elimination *)
  shows "(\<exists>x. F(x)) = (F\<^sub>i\<^sub>n\<^sub>f\<or>(\<exists>r\<in>A. F r)\<or>(\<exists>r\<in>B. F\<epsilon> r)\<or>(\<exists>r\<in>C. F r)\<or>(\<exists>r\<in>D. F\<epsilon> r))"
proof-
  { fix X
    have "(\<exists>(a, b, c)\<in>set X. eq_fun a b c eq les leq neq) = (\<exists>x\<in>F ` \<Union>(roots ` (set X)). x)"
    proof(induction X)
      case Nil
      then show ?case by auto
    next
      case (Cons p X)
      have h1: "(\<exists>x\<in>F ` \<Union> (roots ` set (p # X)). x) = ((\<exists>x\<in>F ` roots p. x) \<or> (\<exists>x\<in>F ` \<Union> (roots ` set X). x))"
        by auto
      have h2 :"(case p of (a,b,c) \<Rightarrow> eq_fun a b c eq les leq neq) = (\<exists>x\<in>F ` roots p. x)"
        apply(cases p) unfolding assms apply simp by linarith
      show ?case  unfolding h1 Cons[symmetric] using h2 by auto
    qed
  }
  then have eq : "\<And>X. (\<exists>(a, b, c)\<in>set X. eq_fun a b c eq les leq neq) = (\<exists>x\<in>F ` \<Union> (roots ` set X). x)" by auto
  { fix X
    have "(\<exists>(a, b, c)\<in>set X. les_fun a b c eq les leq neq) = (\<exists>x\<in>F\<epsilon> ` \<Union>(roots ` (set X)). x)"
    proof(induction X)
      case Nil
      then show ?case by auto
    next
      case (Cons p X)
      have h1: "(\<exists>x\<in>F\<epsilon> ` \<Union> (roots ` set (p # X)). x) = ((\<exists>x\<in>F\<epsilon> ` roots p. x) \<or> (\<exists>x\<in>F\<epsilon> ` \<Union> (roots ` set X). x))"
        by auto
      have h2 :"(case p of (a,b,c) \<Rightarrow> les_fun a b c eq les leq neq) = (\<exists>x\<in>F\<epsilon> ` roots p. x)"
        apply(cases p) unfolding assms apply simp by linarith
      show ?case  unfolding h1 Cons[symmetric] using h2 by auto
    qed
  }
  then have les : "\<And>X. (\<exists>(a, b, c)\<in>set X. les_fun a b c eq les leq neq) = (\<exists>x\<in>F\<epsilon> ` \<Union> (roots ` set X). x)" by auto
  have inf : "(\<forall>(a, b, c)\<in>set eq. a = 0 \<and> b = 0 \<and> c = 0) = (\<forall>x\<in>set eq. case x of (a, b, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c = 0)"
  proof(induction eq)
    case Nil
    then show ?case by auto
  next
    case (Cons p eq)
    then show ?case proof(cases p)
      case (fields a b c)
      show ?thesis unfolding fields using infzeros[of _ a b c] Cons by auto
    qed
  qed
  show ?thesis
    using qe[of "eq" "les" "leq" "neq"]
    using eq[of eq] eq[of leq] les[of les] les[of neq] unfolding inf assms
    by auto
qed

lemma general_qe'' :
  (* Direct substitution F(x) *)
  assumes "S = {(=), (<), (\<le>), (\<noteq>)}"
  assumes "finite (X (=))"
  assumes "finite (X (<))"
  assumes "finite (X (\<le>))"
  assumes "finite (X (\<noteq>))"
  assumes "F = (\<lambda>x. \<forall>rel\<in>S. \<forall>(a,b,c)\<in>(X rel). rel (a*x\<^sup>2+b*x+c) 0)"
    (* Substitution of r+\<epsilon> into F *)
  assumes "F\<epsilon> = (\<lambda>r. \<forall>rel\<in>S. \<forall>(a,b,c)\<in>(X rel). \<exists>y>r.\<forall>x\<in>{r<..y}. rel (a*x\<^sup>2+b*x+c) 0)"
    (* Substitution of -\<infinity> into F *)
  assumes "F\<^sub>i\<^sub>n\<^sub>f = (\<forall>rel\<in>S. \<forall>(a,b,c)\<in>(X rel). \<exists>x. \<forall>y<x. rel (a*y\<^sup>2+b*y+c) 0)"
    (* finds linear or quadratic roots of a polynomial *)
  assumes "roots = (\<lambda>(a,b,c).
     if a=0 \<and> b\<noteq>0 then {-c/b}::real set else
     if a\<noteq>0 \<and> b\<^sup>2-4*a*c\<ge>0 then {(-b+sqrt(b\<^sup>2-4*a*c))/(2*a)}\<union>{(-b-sqrt(b\<^sup>2-4*a*c))/(2*a)} else {})"
    (* all the root of each atom *)
  assumes "A = \<Union>(roots ` ((X (=))))"
  assumes "B = \<Union>(roots ` ((X (<))))"
  assumes "C = \<Union>(roots ` ((X (\<le>))))"
  assumes "D = \<Union>(roots ` ((X (\<noteq>))))"
    (* Quantifier Elimination *)
  shows "(\<exists>x. F(x)) = (F\<^sub>i\<^sub>n\<^sub>f\<or>(\<exists>r\<in>A. F r)\<or>(\<exists>r\<in>B. F\<epsilon> r)\<or>(\<exists>r\<in>C. F r)\<or>(\<exists>r\<in>D. F\<epsilon> r))"
proof-
  define less where "less = (\<lambda>(a::real,b::real,c::real).\<lambda>(a',b',c'). a<a'\<or> (a=a'\<and> (b<b'\<or>(b=b'\<and>c<c'))))"
  define leq where "leq = (\<lambda>x.\<lambda>y. x=y \<or> less x y)"
  have linorder: "class.linorder leq less"
    unfolding class.linorder_def class.order_def class.preorder_def class.order_axioms_def class.linorder_axioms_def
      less_def leq_def by auto
  show ?thesis
    using assms(6-8) unfolding assms(1) apply simp
    using general_qe'[OF _ _ _ assms(9), of F "List.linorder.sorted_list_of_set leq (X (=))" "List.linorder.sorted_list_of_set leq (X (<))" "List.linorder.sorted_list_of_set leq (X (\<le>))" "List.linorder.sorted_list_of_set leq (X (\<noteq>))" F\<epsilon> F\<^sub>i\<^sub>n\<^sub>f A B C D]
    unfolding List.linorder.set_sorted_list_of_set[OF linorder assms(2)] List.linorder.set_sorted_list_of_set[OF linorder assms(3)] List.linorder.set_sorted_list_of_set[OF linorder assms(4)] List.linorder.set_sorted_list_of_set[OF linorder assms(5)]
    using assms(10-13)by auto
qed


theorem general_qe :
  (* finite sets of atoms involving = < \<le> and \<noteq>*)
  assumes "R = {(=), (<), (\<le>), (\<noteq>)}"
  assumes "\<forall>rel\<in>R. finite (Atoms rel)"
    (* Direct substitution F(x) *)
  assumes "F = (\<lambda>x. \<forall>rel\<in>R. \<forall>(a,b,c)\<in>(Atoms rel). rel (a*x\<^sup>2+b*x+c) 0)"
    (* Substitution of r+\<epsilon> into F *)
  assumes "F\<epsilon> = (\<lambda>r. \<forall>rel\<in>R. \<forall>(a,b,c)\<in>(Atoms rel). \<exists>y>r.\<forall>x\<in>{r<..y}. rel (a*x\<^sup>2+b*x+c) 0)"
    (* Substitution of -\<infinity> into F *)
  assumes "F\<^sub>i\<^sub>n\<^sub>f = (\<forall>rel\<in>R. \<forall>(a,b,c)\<in>(Atoms rel). \<exists>x. \<forall>y<x. rel (a*y\<^sup>2+b*y+c) 0)"
    (* finds linear or quadratic roots of a polynomial *)
  assumes "roots = (\<lambda>(a,b,c).
     if a=0 \<and> b\<noteq>0 then {-c/b} else
     if a\<noteq>0 \<and> b\<^sup>2-4*a*c\<ge>0 then {(-b+sqrt(b\<^sup>2-4*a*c))/(2*a)}\<union>{(-b-sqrt(b\<^sup>2-4*a*c))/(2*a)} else {})"
    (* Quantifier Elimination *)
  shows "(\<exists>x. F(x)) = 
            (F\<^sub>i\<^sub>n\<^sub>f \<or>
            (\<exists>r\<in>\<Union>(roots ` (Atoms (=) \<union> Atoms (\<le>))). F r) \<or>
            (\<exists>r\<in>\<Union>(roots ` (Atoms (<) \<union> Atoms (\<noteq>))). F\<epsilon> r))"
  using general_qe''[OF assms(1) _ _ _ _ assms(3-6) refl refl refl refl]
  using assms(2) unfolding assms(1) 
  by auto

end