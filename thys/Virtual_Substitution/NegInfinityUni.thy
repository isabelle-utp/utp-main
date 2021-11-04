theory NegInfinityUni
  imports UniAtoms NegInfinity QE
begin

fun allZero' :: "real * real * real \<Rightarrow> atomUni fmUni" where
  "allZero' (a,b,c) = AndUni(AndUni(AtomUni(EqUni(0,0,a))) (AtomUni(EqUni(0,0,b)))) (AtomUni(EqUni(0,0,c)))"

lemma convert_allZero : 
  assumes "convert_poly var p (xs'@x#xs) = Some p'"
  assumes "length xs' = var"
  shows "eval (allZero p var) (xs'@x#xs) = evalUni (allZero' p') x"
proof(cases p')
  case (fields a b c)
  then show ?thesis proof(cases "MPoly_Type.degree p var = 0")
    case True
    then show ?thesis
      using assms fields
      by(simp add:eval_list_conj isovar_greater_degree)
  next
    case False
    then have nonzero : "MPoly_Type.degree p var \<noteq> 0" by auto
    then show ?thesis
    proof(cases "MPoly_Type.degree p var = 1")
      case True
      then show ?thesis
        using assms fields
        apply(simp add:eval_list_conj isovar_greater_degree)
        by (metis)
    next
      case False
      then have degree2 : "MPoly_Type.degree p var = 2" using degree_convert_eq[OF assms(1)] nonzero by auto
      then show ?thesis
        using assms
        apply(simp add:eval_list_conj isovar_greater_degree)
        using insertion_isovarspars_free list_update_code(2)
        apply auto
        by (metis One_nat_def Suc_1 less_2_cases less_Suc_eq numeral_3_eq_3)
    qed
  qed
qed



fun alternateNegInfinity' :: "real * real * real \<Rightarrow> atomUni fmUni" where
  "alternateNegInfinity' (a,b,c) = 
OrUni(AtomUni(LessUni(0,0,a)))(
AndUni(AtomUni(EqUni(0,0,a))) (
  OrUni(AtomUni(LessUni(0,0,-b)))(
  AndUni(AtomUni(EqUni(0,0,b)))(
    AtomUni(LessUni(0,0,c))
  ))
))
"

lemma convert_alternateNegInfinity : 
  assumes "convert_poly var p (xs'@x#xs) = Some X"
  assumes "length xs' = var"
  shows "eval (alternateNegInfinity p var) (xs'@x#xs) = evalUni (alternateNegInfinity' X) x"
proof(cases X)
  case (fields a b c)
  then show ?thesis proof(cases "MPoly_Type.degree p var = 0")
    case True
    then show ?thesis
      using assms
      apply (simp add: isovar_greater_degree)
      apply auto
      apply (metis aEval.simps(2) eval.simps(1) eval_and eval_false eval_or  mult_one_left)
      by (metis aEval.simps(2) eval.simps(1) eval_or  mult_one_left)
  next
    case False
    then have nonzero : "MPoly_Type.degree p var \<noteq> 0" by auto
    then show ?thesis
    proof(cases "MPoly_Type.degree p var = 1")
      case True
      have letbind: "eval
     (let a_n = isolate_variable_sparse p var (Suc 0)
      in or (fm.Atom (Less (Const (- 1) * a_n)))
          (and (fm.Atom (Eq a_n))
            (let a_n = isolate_variable_sparse p var 0
             in or (fm.Atom (Less (Const 1 * a_n))) (and (fm.Atom (Eq a_n)) FalseF))))
     (xs'@x#xs) = 
    eval
     (or (fm.Atom (Less (Const (- 1) * (isolate_variable_sparse p var (Suc 0)))))
          (and (fm.Atom (Eq (isolate_variable_sparse p var (Suc 0))))
            (or (fm.Atom (Less (Const 1 * (isolate_variable_sparse p var 0)))) (and (fm.Atom (Eq (isolate_variable_sparse p var 0))) FalseF))))
     (xs'@x#xs)"
        by meson 
      show ?thesis
        using assms True unfolding fields
        by (simp add: isovar_greater_degree letbind eval_or eval_and insertion_mult insertion_const)
    next
      case False
      then have degree2 : "MPoly_Type.degree p var = 2" using degree_convert_eq[OF assms(1)] nonzero by auto
      have "[0..<3] = [0,1,2]"
        by (simp add: upt_rec)
      then have unfold : " (foldl
       (\<lambda>F i. let a_n = isolate_variable_sparse p var i
               in or (fm.Atom (Less ((if i mod 2 = 0 then Const 1 else Const (- 1)) * a_n)))
                   (and (fm.Atom (Eq a_n)) F))
       FalseF [0..<3]) =  
     (let a_n = isolate_variable_sparse p var 2
               in or (fm.Atom (Less ((Const 1) * a_n)))
                   (and (fm.Atom (Eq a_n))
       (let a_n = isolate_variable_sparse p var (Suc 0)
      in or (fm.Atom (Less (Const (- 1) * a_n)))
          (and (fm.Atom (Eq a_n))
            (let a_n = isolate_variable_sparse p var 0
             in or (fm.Atom (Less (Const 1 * a_n))) (and (fm.Atom (Eq a_n)) FalseF))))))" 
        by auto
      have letbind : "eval
     (foldl
       (\<lambda>F i. let a_n = isolate_variable_sparse p var i
               in or (fm.Atom (Less ((if i mod 2 = 0 then Const 1 else Const (- 1)) * a_n)))
                   (and (fm.Atom (Eq a_n)) F))
       FalseF [0..<3]) (xs'@x#xs) = 
      eval
     
(or (fm.Atom (Less ( Const 1 * (isolate_variable_sparse p var 2))))
                   (and (fm.Atom (Eq (isolate_variable_sparse p var 2)))
(or (fm.Atom (Less (Const (- 1) * (isolate_variable_sparse p var (Suc 0)))))
          (and (fm.Atom (Eq (isolate_variable_sparse p var (Suc 0))))
            (or (fm.Atom (Less (Const 1 * (isolate_variable_sparse p var 0)))) (and (fm.Atom (Eq (isolate_variable_sparse p var 0))) FalseF))))))
(xs'@x#xs)" apply (simp add:unfold) by metis
      show ?thesis
        using degree2 assms unfolding fields by (simp add: isovar_greater_degree eval_or eval_and letbind insertion_mult insertion_const)
    qed
  qed
qed



fun substNegInfinityUni :: "atomUni \<Rightarrow> atomUni fmUni" where
  "substNegInfinityUni (EqUni p) = allZero' p " |
  "substNegInfinityUni (LessUni p) = alternateNegInfinity' p"|
  "substNegInfinityUni (LeqUni p) = OrUni (alternateNegInfinity' p) (allZero' p)"|
  "substNegInfinityUni (NeqUni p) = negUni (allZero' p)"


lemma convert_substNegInfinity : 
  assumes "convert_atom var A (xs'@x#xs) = Some(A')"
  assumes "length xs' = var"
  shows "eval (substNegInfinity var A) (xs'@x#xs) = evalUni (substNegInfinityUni A') x"
  using assms
proof(cases A)
  case (Less p)
  have "\<exists>X. convert_poly var p (xs' @ x # xs) = Some X" using assms Less apply(cases "MPoly_Type.degree p var < 3") by (simp_all)
  then obtain X where X_def: "convert_poly var p (xs' @ x # xs) = Some X" by auto
  then have A' : "A' = LessUni X" using assms Less apply(cases "MPoly_Type.degree p var < 3") by (simp_all)
  show ?thesis unfolding Less substNegInfinity.simps
    unfolding convert_alternateNegInfinity[OF X_def assms(2)] A'
    apply(cases X) by simp
next
  case (Eq p)
  then show ?thesis using assms convert_allZero by auto
next
  case (Leq p)
  define p' where "p' = (case convert_poly var p (xs'@x#xs) of Some p' \<Rightarrow> p')"
  have A'_simp :  "A' = LeqUni p'"
    using assms Leq
    using p'_def by auto 
  have allZ : "eval (allZero p var) (xs'@x#xs) = evalUni (allZero' p') x" using convert_allZero
    using Leq assms p'_def by auto 
  have altNeg : "eval (alternateNegInfinity p var) (xs'@x#xs) = evalUni (alternateNegInfinity' p') x" using convert_alternateNegInfinity
    using Leq assms p'_def by auto
  show ?thesis
    unfolding Leq substNegInfinity.simps eval_Or A'_simp substNegInfinityUni.simps evalUni.simps
    using allZ altNeg by auto
next
  case (Neq p)
  then show ?thesis using assms convert_allZero convert_neg by auto
qed

lemma change_eval_eq:
  fixes x y:: "real"
  assumes "((aEvalUni (EqUni(a,b,c)) x \<noteq> aEvalUni (EqUni(a,b,c)) y) \<and> x < y)"
  shows "(\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
  using assms by auto
lemma change_eval_lt:
  fixes x y:: "real"
  assumes "((aEvalUni (LessUni (a,b,c)) x \<noteq> aEvalUni (LessUni (a,b,c)) y) \<and> x < y)"
  shows "(\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
proof - 
  let ?p = "[:c, b, a:]"
  have "sign ?p x \<noteq> sign ?p y"
    using assms unfolding sign_def 
    apply (simp add: distrib_left mult.commute mult.left_commute power2_eq_square)
    by linarith
  then have "(\<exists>w \<in> (root_list ?p). x \<le> w \<and> w \<le> y)" using changes_sign 
      assms by auto
  then obtain w where w_prop: "w \<in> (root_list ?p) \<and> x \<le> w \<and> w \<le> y" by auto
  then have "a*w^2 + b*w + c = 0" unfolding root_list_def 
    using add.commute distrib_right mult.assoc mult.commute power2_eq_square
    using quadratic_poly_eval by force
  then show ?thesis using w_prop by auto
qed

lemma no_change_eval_lt:
  fixes x y:: "real"
  assumes "x < y"
  assumes "\<not>(\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
  shows "((aEvalUni (LessUni (a,b,c)) x = aEvalUni (LessUni (a,b,c)) y))"
  using change_eval_lt
  using assms(1) assms(2) by blast 


lemma change_eval_neq:
  fixes x y:: "real"
  assumes "((aEvalUni (NeqUni (a,b,c)) x \<noteq> aEvalUni (NeqUni (a,b,c)) y) \<and> x < y)"
  shows "(\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
  using assms by auto 

lemma change_eval_leq:
  fixes x y:: "real"
  assumes "((aEvalUni (LeqUni (a,b,c)) x \<noteq> aEvalUni (LeqUni (a,b,c)) y) \<and> x < y)"
  shows "(\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
proof - 
  let ?p = "[:c, b, a:]"
  have "sign ?p x \<noteq> sign ?p y"
    using assms unfolding sign_def
    apply (simp add: distrib_left mult.commute mult.left_commute power2_eq_square)
    by linarith
  then have "(\<exists>w \<in> (root_list ?p). x \<le> w \<and> w \<le> y)" using changes_sign 
      assms by auto
  then obtain w where w_prop: "w \<in> (root_list ?p) \<and> x \<le> w \<and> w \<le> y" by auto
  then have "a*w^2 + b*w + c = 0" unfolding root_list_def
    using add.commute distrib_right mult.assoc mult.commute power2_eq_square
    using quadratic_poly_eval by force  
  then show ?thesis using w_prop by auto
qed

lemma change_eval:
  fixes x y:: "real"
  fixes At:: "atomUni" 
  assumes xlt: "x < y"
  assumes noteq: "((aEvalUni At) x \<noteq> aEvalUni (At) y)"
  assumes "getPoly At = (a, b, c)"
  shows "(\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
proof - 
  have four_types: "At = (EqUni (a,b,c)) \<or> At = (LessUni (a,b,c)) \<or> At = (LeqUni (a,b,c)) \<or> At = (NeqUni (a,b,c))"
    using getPoly.elims assms(3) by force 
  have eq_h: "At = (EqUni (a,b,c)) \<longrightarrow> (\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
    using assms(1) assms(2) change_eval_eq 
    by blast
  have less_h: "At = (LessUni(a,b,c)) \<longrightarrow> (\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
    using change_eval_lt assms
    by blast
  have leq_h: "At = (LeqUni(a,b,c)) \<longrightarrow> (\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
    using change_eval_leq assms
    by blast
  have neq_h: "At = (NeqUni(a,b,c)) \<longrightarrow> (\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
    using change_eval_neq assms
    by blast
  show ?thesis
    using four_types eq_h less_h leq_h neq_h
    by blast 
qed 

lemma no_change_eval:
  fixes x y:: "real"
  assumes "getPoly At = (a, b, c)"
  assumes "x < y"
  assumes "\<not>(\<exists>w. x \<le> w \<and> w \<le> y \<and> a*w^2 + b*w + c = 0)"
  shows  "((aEvalUni At) x = aEvalUni (At) y \<and> x < y)"
  using change_eval
  using assms(1) assms(2) assms(3) by blast 


lemma same_eval'' :
  assumes "getPoly At = (a, b, c)"
  assumes nonz: "a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0"
  shows "\<exists>x. \<forall>y<x. (aEvalUni At y = aEvalUni At x)"
proof - 
  let ?p = "[:c, b, a:]"
  have poly_eval: "\<forall>y. poly ?p y = a*y^2 + b*y + c" 
    by (simp add: distrib_left power2_eq_square) 
  have "?p \<noteq> 0" using nonz by auto
  then have "finite {y. poly ?p y = 0}"
    using poly_roots_finite
    by blast
  then have "finite {y. c + (a * y\<^sup>2 + b * y) = 0} \<Longrightarrow>
    \<forall>y. y * (b + y * a) = a * y\<^sup>2 + b * y \<Longrightarrow>
    finite {y. a * y\<^sup>2 + b * y + c = 0}"
  proof -
    assume a1: "finite {y. c + (a * y\<^sup>2 + b * y) = 0}"
    have "\<forall>x0. c + (a * x0\<^sup>2 + b * x0) = a * x0\<^sup>2 + b * x0 + c"
      by simp
    then show ?thesis
      using a1 by presburger
  qed 
  then have finset: "finite {y. a*y^2 + b*y + c = 0}" 
    using poly_eval
    by (metis \<open>finite {y. poly [:c, b, a:] y = 0}\<close> poly_roots_set_same) 
  then have "\<exists>x. (\<forall>y. a*y^2 + b*y + c = 0 \<longrightarrow> x < y)" 
  proof - 
    let ?l = "sorted_list_of_set {y. a*y^2 + b*y + c = 0}"
    have "\<exists>x. x < ?l ! 0" 
      using infzeros nonz by blast 
    then obtain x where x_prop: "x < ?l! 0" by auto
    then have "\<forall> y. List.member ?l y \<longrightarrow> x < y"
    proof clarsimp
      fix y
      assume "List.member ?l y"
      then have "\<exists>n. n < length ?l \<and> ?l ! n = y"
        by (meson in_set_conv_nth in_set_member)
      then obtain n where n_prop: "n < length ?l \<and> ?l ! n = y"
        by auto
      have h: "\<forall>n < length ?l. ?l ! n \<ge> ?l !0" using sorted_iff_nth_mono
        using sorted_sorted_list_of_set by blast
      then have h: "y \<ge> ?l ! 0" using n_prop by auto
      then show "x < y" using x_prop by auto
    qed
    then show ?thesis
      using finset set_sorted_list_of_set in_set_member
      by (metis (mono_tags, lifting) mem_Collect_eq)
  qed
  then obtain x where x_prop: "(\<forall>y. a*y^2 + b*y + c = 0 \<longrightarrow> x < y)" by auto
  then have same_as: "\<forall>y<x. (aEvalUni At y = aEvalUni At x)"
    using no_change_eval change_eval assms
  proof -
    have f1: "\<forall>x0. (x0 < x) = (\<not> 0 \<le> x0 + - 1 * x)"
      by auto
    have f2: "(0 \<le> - 1 * x + v0_0) = (x + - 1 * v0_0 \<le> 0)"
      by auto
    have f3: "v0_0 + - 1 * x = - 1 * x + v0_0"
      by auto
    have f4: "\<forall>x0 x1 x2 x3. (x3::real) * x0\<^sup>2 + x2 * x0 + x1 = x1 + x3 * x0\<^sup>2 + x2 * x0"
      by auto
    have f5: "\<forall>x3 x4 x5. (aEvalUni x3 x5 \<noteq> aEvalUni x3 x4) = ((\<not> aEvalUni x3 x5) = aEvalUni x3 x4)"
      by fastforce
    have f6: "\<forall>x0 x1 x2 x3 x4 x5. (x5 < x4 \<and> (\<not> aEvalUni x3 x5) = aEvalUni x3 x4 \<and> getPoly x3 = (x2, x1, x0) \<longrightarrow> (\<exists>v6\<ge>x5. v6 \<le> x4 \<and> x0 + x2 * v6\<^sup>2 + x1 * v6 = 0)) = ((\<not> x5 < x4 \<or> (\<not> aEvalUni x3 x5) \<noteq> aEvalUni x3 x4 \<or> getPoly x3 \<noteq> (x2, x1, x0)) \<or> (\<exists>v6\<ge>x5. v6 \<le> x4 \<and> x0 + x2 * v6\<^sup>2 + x1 * v6 = 0))"
      by fastforce
    have f7: "\<forall>x0 x5. ((x0::real) \<le> x5) = (x0 + - 1 * x5 \<le> 0)"
      by auto
    have f8: "\<forall>x0 x6. ((x6::real) \<le> x0) = (0 \<le> x0 + - 1 * x6)"
      by auto
    have "\<forall>x4 x5. ((x5::real) < x4) = (\<not> x4 + - 1 * x5 \<le> 0)"
      by auto
    then have "(\<forall>r ra a rb rc rd. r < ra \<and> aEvalUni a r \<noteq> aEvalUni a ra \<and> getPoly a = (rb, rc, rd) \<longrightarrow> (\<exists>re\<ge>r. re \<le> ra \<and> rb * re\<^sup>2 + rc * re + rd = 0)) = (\<forall>r ra a rb rc rd. (ra + - 1 * r \<le> 0 \<or> (\<not> aEvalUni a r) \<noteq> aEvalUni a ra \<or> getPoly a \<noteq> (rb, rc, rd)) \<or> (\<exists>re. 0 \<le> re + - 1 * r \<and> re + - 1 * ra \<le> 0 \<and> rd + rb * re\<^sup>2 + rc * re = 0))"
      using f8 f7 f6 f5 f4 by presburger
    then have f9: "\<forall>r ra a rb rc rd. (ra + - 1 * r \<le> 0 \<or> (\<not> aEvalUni a r) \<noteq> aEvalUni a ra \<or> getPoly a \<noteq> (rb, rc, rd)) \<or> (\<exists>re. 0 \<le> re + - 1 * r \<and> re + - 1 * ra \<le> 0 \<and> rd + rb * re\<^sup>2 + rc * re = 0)"
      by (meson change_eval)
    obtain rr :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
      "\<forall>x0 x1 x2 x4 x5. (\<exists>v6. 0 \<le> v6 + - 1 * x5 \<and> v6 + - 1 * x4 \<le> 0 \<and> x0 + x2 * v6\<^sup>2 + x1 * v6 = 0) = (0 \<le> rr x0 x1 x2 x4 x5 + - 1 * x5 \<and> rr x0 x1 x2 x4 x5 + - 1 * x4 \<le> 0 \<and> x0 + x2 * (rr x0 x1 x2 x4 x5)\<^sup>2 + x1 * rr x0 x1 x2 x4 x5 = 0)"
      by moura
    then have f10: "\<forall>r ra a rb rc rd. ra + - 1 * r \<le> 0 \<or> aEvalUni a r = aEvalUni a ra \<or> getPoly a \<noteq> (rb, rc, rd) \<or> r + - 1 * rr rd rc rb ra r \<le> 0 \<and> 0 \<le> ra + - 1 * rr rd rc rb ra r \<and> rd + rb * (rr rd rc rb ra r)\<^sup>2 + rc * rr rd rc rb ra r = 0"
      using f9 by simp
    have f11: "(rr c b a x v0_0 + - 1 * x \<le> 0) = (0 \<le> x + - 1 * rr c b a x v0_0)"
      by force
    have "\<forall>x0. (x < x0) = (\<not> x0 + - 1 * x \<le> 0)"
      by auto
    then have f12: "\<forall>r. c + a * r\<^sup>2 + b * r \<noteq> 0 \<or> \<not> r + - 1 * x \<le> 0"
      using x_prop by auto
    obtain rra :: real where
      "(\<exists>v0. \<not> 0 \<le> v0 + - 1 * x \<and> aEvalUni At v0 \<noteq> aEvalUni At x) = (\<not> 0 \<le> rra + - 1 * x \<and> aEvalUni At rra \<noteq> aEvalUni At x)"
      by moura
    then show ?thesis
      using f12 f11 f10 f3 f2 f1
    proof -
      have f1: "\<forall>x0. (x0 < x) = (\<not> 0 \<le> x0 + - 1 * x)"
        by auto
      have f2: "(0 \<le> v0_0a + - 1 * x) = (x + - 1 * v0_0a \<le> 0)"
        by auto
      have f3: "(rr c b a x v0_0a + - 1 * x \<le> 0) = (0 \<le> x + - 1 * rr c b a x v0_0a)"
        by auto
      obtain rrb :: real where
        "(\<exists>v0. \<not> 0 \<le> v0 + - 1 * x \<and> aEvalUni At v0 \<noteq> aEvalUni At x) = (\<not> 0 \<le> rrb + - 1 * x \<and> aEvalUni At rrb \<noteq> aEvalUni At x)"
        by blast
      then show ?thesis
        using f3 f2 f1 assms(1) f10 f12
        by smt
    qed
  qed
  then show ?thesis by auto
qed


lemma inequality_case : "(\<exists>(x::real). \<forall>(y::real)<x. (a::real) * y\<^sup>2 + (b::real) * y + (c::real) < 0) =
    (a < 0 \<or> a = 0 \<and> (0 < b \<or> b = 0 \<and> c < 0))"
proof-
  let ?At = "(LessUni (a, b, c))"
  have firsth : "\<And>x. (\<forall>y<x. a * y\<^sup>2 + b * y + c < 0 \<Longrightarrow> a\<le>0)"
  proof -
    fix x
    assume lt: "\<forall>y<x. a * y\<^sup>2 + b * y + c < 0"
    have "\<exists>w. \<forall>y < w. y^2 > (-b/a)*y - c/a"  using ysq_dom_y_plus_coeff[where b = "-b/a", where c = "-c/a"]
      by auto   
    then have gtdomhelp: "a > 0 \<Longrightarrow> \<exists>w. \<forall>y < w. a*y^2 > a*((-b/a)*y - c/a)"
      by auto
    have "\<forall>y. (a > 0 \<longrightarrow> a*((-b/a)*y - c/a) = -b*y - c)"
      by (simp add: right_diff_distrib') 
    then have gtdom: "a > 0 \<Longrightarrow> \<exists>w.\<forall>y < w. a*y^2 > -b*y - c"
      using gtdomhelp
      by simp 
    then have " a > 0 \<Longrightarrow> False"
    proof - 
      assume "a > 0"
      then have "\<exists>w.\<forall>y < w. a*y^2 > -b*y - c" using gtdom by auto
      then obtain w where w_prop: "\<forall>y < w. a*y^2 + b*y + c > 0"
        by fastforce 
      let ?mn = "min w x - 1"
      have gtz: "a*?mn^2 + b*?mn + c > 0" using w_prop
        by auto
      have ltz: "a*?mn^2 + b*?mn + c < 0" using lt by auto
      then show "False" using gtz ltz by auto
    qed
    then show "a \<le> 0"
      by fastforce 
  qed
  have bleq0 : "\<And>x. (\<forall>y<x. b * y + c < 0 \<Longrightarrow> b\<ge>0)"
  proof -
    fix x
    assume lt: "\<forall>y<x. b * y + c < 0"
    have gtdom: "b < 0 \<Longrightarrow> \<exists>w.\<forall>y < w. b*y > - c"
      by (metis mult.commute neg_less_divide_eq)
    then have "b < 0 \<Longrightarrow> False"
    proof - 
      assume "b < 0"
      then have "\<exists>w.\<forall>y < w. b*y > - c" using gtdom by auto
      then obtain w where w_prop: "\<forall>y < w .b*y + c > 0"
        by fastforce 
      let ?mn = "min w x - 1"
      have gtz: "b*?mn + c > 0" using w_prop
        by auto
      have ltz: "b*?mn + c < 0" using lt by auto
      then show "False" using gtz ltz by auto
    qed
    then show "b \<ge> 0"
      by fastforce 
  qed
  have secondh: "\<And>x. (\<forall>y<x. a * y\<^sup>2 + b * y + c < 0 \<Longrightarrow> \<not> a < 0 \<Longrightarrow> \<not> 0 < b \<Longrightarrow> b = 0)"
    using firsth bleq0
    by (metis add.commute add.right_neutral less_eq_real_def mult_zero_class.mult_zero_left) 
  have thirdh : "\<And>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0 \<Longrightarrow> \<not> a < 0 \<Longrightarrow> \<not> 0 < b \<Longrightarrow> c < 0"
    using firsth secondh add.commute add.right_neutral infzeros mult_zero_class.mult_zero_left not_numeral_le_zero order_refl
    by (metis less_eq_real_def)
  have fourthh : "a < 0 \<Longrightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0"
  proof - 
    assume aleq: "a < 0"
    have "\<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> y^2 > (-b/a)*y + (-c/a))"
      using ysq_dom_y_plus_coeff[where b = "-b/a", where c = "-c/a"]
      by blast 
    then have hyp:"\<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> a*y^2 \<le> a*(-b/a)*y + a*(-c/a))"
      by (metis (no_types, hide_lams) \<open>a < 0\<close> distrib_left less_eq_real_def linorder_not_le mult.assoc mult_less_cancel_left)
    have "\<forall>y. a*(-b/a)*y + a*(-c/a) = -b*y -c"
      using \<open>a < 0\<close> by auto
    then have "\<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> a*y^2 \<le> -b*y - c)"
      using hyp by auto
    then have "\<exists>(w::real). \<forall>(y::real). (y < w \<longrightarrow> a*y^2 + b*y + c \<le> 0)"
      by (metis add.commute add_uminus_conv_diff le_diff_eq mult_minus_left real_add_le_0_iff)
    then obtain w where w_prop: "\<forall>(y::real). (y < w \<longrightarrow> a*y^2 + b*y + c \<le> 0)" by auto
    have "\<exists>x. \<forall>y < x. aEvalUni ?At x = aEvalUni ?At y" using same_eval''
    proof -
      have f1: "\<forall>x0 x1. ((x0::real) < x1) = (\<not> 0 \<le> x0 + - 1 * x1)"
        by linarith
      have "a \<noteq> 0"
        using \<open>a < 0\<close> by force
      then obtain rr :: "atomUni \<Rightarrow> real" where
        "\<forall>r. 0 \<le> r + - 1 * rr (LessUni (a, b, c)) \<or> aEvalUni (LessUni (a, b, c)) r = aEvalUni (LessUni (a, b, c)) (rr (LessUni (a, b, c)))"
        using f1 by (metis getPoly.simps(4) same_eval'')
      then show ?thesis
        using f1 by meson
    qed
    then obtain x where x_prop: "\<forall>y < x. aEvalUni ?At x = aEvalUni ?At y" by auto
    let ?mn = "min x w - 1"
    have "\<forall>y < ?mn.  aEvalUni ?At y = True \<or> aEvalUni ?At y = False"
      using x_prop by auto
    have "\<forall> y < ?mn. aEvalUni ?At y = False \<longrightarrow> a*y^2 + b*y + c \<ge> 0"
      by auto
    then have "\<And>y. \<forall>y<w. a * y\<^sup>2 + b * y + c \<le> 0 \<Longrightarrow>
         y < min x w - 1 \<Longrightarrow>
         \<not> a * y\<^sup>2 + b * y + c < 0 \<Longrightarrow>
         a * y\<^sup>2 + b * y + c = 0"
    proof -
      fix y :: real
      assume a1: "y < min x w - 1"
      assume a2: "\<not> a * y\<^sup>2 + b * y + c < 0"
      assume a3: "\<forall>y<w. a * y\<^sup>2 + b * y + c \<le> 0"
      have "y < w"
        using a1 by linarith
      then show "a * y\<^sup>2 + b * y + c = 0"
        using a3 a2 less_eq_real_def by blast
    qed 
    then have "\<forall> y < ?mn. aEvalUni ?At y = False \<longrightarrow> a*y^2 + b*y + c = 0"
      using w_prop by auto    
    then have "\<forall> y < ?mn. aEvalUni ?At y = False \<Longrightarrow> False" using infzeros aleq
      by (metis power_zero_numeral zero_less_power2)
    then have "\<forall> y < ?mn. aEvalUni ?At y = True"
    proof -
      { fix rr :: real
        have "\<forall>r ra. (ra::real) < r \<or> \<not> ra < r + - 1"
          by linarith
        then have "\<not> rr < min x w - 1 \<or> aEvalUni (LessUni (a, b, c)) rr"
          by (metis (no_types) \<open>\<forall>y<min x w - 1. aEvalUni (LessUni (a, b, c)) y = False \<Longrightarrow> False\<close> ab_group_add_class.ab_diff_conv_add_uminus less_eq_real_def min_less_iff_disj not_le x_prop) }
      then show ?thesis
        by blast
    qed 
    then show ?thesis by auto
  qed
  have fifthh : "b > 0 \<Longrightarrow> \<exists>x. \<forall>y<x. b * y + c < 0"
  proof-
    assume bh : "b > 0"
    show "\<exists>x. \<forall>y<x. b * y + c < 0"
      apply(rule exI[where x="-c/b"])
      apply auto
      using bh
      by (simp add: mult.commute pos_less_minus_divide_eq) 
  qed
  show ?thesis
    apply(auto)
    using firsth apply simp
    using secondh apply simp 
    using thirdh apply simp
    using fourthh apply simp
    using fifthh by simp
qed

lemma inequality_case_geq : "(\<exists>(x::real). \<forall>(y::real)<x. (a::real) * y\<^sup>2 + (b::real) * y + (c::real) > 0) =
    (a > 0 \<or> a = 0 \<and> (0 > b \<or> b = 0 \<and> c > 0))"
proof - 
  have s1: "\<forall>y. - 1 * a * y\<^sup>2 + - 1 * b * y + - 1 * c < 0 \<longleftrightarrow>  a * y\<^sup>2 +  b * y +  c > 0"
    by auto
  have s2: "(- 1 * a < 0 \<or> - 1 * a = 0 \<and> (0 < - 1 * b \<or> - 1 * b = 0 \<and> - 1 * c < 0)) \<longleftrightarrow>
   (a > 0 \<or> a = 0 \<and> (0 > b \<or>  b = 0 \<and> c > 0))  "
    by auto
  have "(\<exists>x. \<forall>y<x. - 1 * a * y\<^sup>2 + - 1 * b * y + - 1 * c < 0) =
  (- 1 * a < 0 \<or> - 1 * a = 0 \<and> (0 < - 1 * b \<or> - 1 * b = 0 \<and> - 1 * c < 0))"
    using inequality_case[where a = "-1*a", where b = "-1*b", where c= "-1*c"]
    by auto
  then show ?thesis
    using s1 s2 by auto
qed

lemma infinity_evalUni_LessUni : "(\<exists>x. \<forall>y<x. aEvalUni (LessUni p) y) = (evalUni (substNegInfinityUni (LessUni p)) x)"
proof(cases p)
  case (fields a b c)
  show ?thesis 
    unfolding fields  apply simp
    using inequality_case[of a b c] .
qed

lemma infinity_evalUni_EqUni : "(\<exists>x. \<forall>y<x. aEvalUni (EqUni p) y) = (evalUni (substNegInfinityUni (EqUni p)) x)"
proof(cases p)
  case (fields a b c)
  show ?thesis
    using infzeros[of _ a b c] by(auto simp add: fields)
qed

lemma infinity_evalUni_NeqUni : "(\<exists>x. \<forall>y<x. aEvalUni (NeqUni p) y) = (evalUni (substNegInfinityUni (NeqUni p)) x)"
proof(cases p)
  case (fields a b c)
  show ?thesis
    unfolding fields  apply simp 
    using inequality_case[of a b c] 
    using inequality_case_geq[of a b c]
    by (metis less_numeral_extra(3) linorder_neqE_linordered_idom mult_eq_0_iff)

qed

lemma infinity_evalUni_LeqUni : "(\<exists>x. \<forall>y<x. aEvalUni (LeqUni p) y) = (evalUni (substNegInfinityUni (LeqUni p)) x)"
proof(cases p)
  case (fields a b c)
  show ?thesis
    unfolding fields  apply simp 
  proof -
    have h1: "((\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or> (\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c = 0)) \<longrightarrow> (\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0)"
      using less_eq_real_def
      by auto
    have h2: "(\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) \<Longrightarrow> ((\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or> (\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c = 0))"
    proof -
      assume a1: "(\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0)"
      have "\<not>(\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c = 0) \<Longrightarrow> (\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) " 
      proof - 
        assume a2: "\<not>(\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c = 0)"
        then have "a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0" by auto
        then have "(a < 0 \<or> a = 0 \<and> (0 < b \<or> b = 0 \<and> c < 0))"
        proof - 
          have x1: "a > 0 \<Longrightarrow> False"
          proof - 
            assume "a > 0"
            then have "(\<exists>(x::real). \<forall>(y::real)<x. (a::real) * y\<^sup>2 + (b::real) * y + (c::real) > 0)" using inequality_case_geq
              by auto
            then  show ?thesis
              using a1 
              by (meson a2 linorder_not_le min_less_iff_conj)  
          qed
          then have x2: "a = 0 \<and> 0 > b \<Longrightarrow> False"
          proof - 
            assume "a = 0 \<and> 0 > b"
            then have "(\<exists>(x::real). \<forall>(y::real)<x. (a::real) * y\<^sup>2 + (b::real) * y + (c::real) > 0)" using inequality_case_geq
              by blast
            then show ?thesis
              using a1
              by (meson a2 linorder_not_le min_less_iff_conj) 
          qed
          then have x3: "a = 0 \<and> b = 0 \<and> c > 0 \<Longrightarrow> False "
            using a1 a2 by auto  
          show ?thesis using x1 x2 x3
            by (meson \<open>a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0\<close> linorder_neqE_linordered_idom) 
        qed
        then show "(\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0)" using inequality_case
          by auto
      qed
      then show ?thesis
        by auto
    qed
    have "(\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) = (\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c < 0) \<or> (\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c = 0)"
      using h1 h2 by auto
    then show "(\<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c \<le> 0) =
    (a < 0 \<or> a = 0 \<and> (0 < b \<or> b = 0 \<and> c < 0) \<or> a = 0 \<and> b = 0 \<and> c = 0)"
      using inequality_case[of a b c] infzeros[of _ a b c] by auto
  qed
qed

text "This is the vertical translation for substNegInfinityUni where we represent the virtual
substution of negative infinity in the univariate case"
lemma infinity_evalUni :
  shows "(\<exists>x. \<forall>y<x. aEvalUni At y) = (evalUni (substNegInfinityUni At) x)"
proof(cases At)
  case (LessUni p)
  then show ?thesis using infinity_evalUni_LessUni by auto
next
  case (EqUni p)
  then show ?thesis using infinity_evalUni_EqUni by auto
next
  case (LeqUni p)
  then show ?thesis using infinity_evalUni_LeqUni by auto
next
  case (NeqUni p)
  then show ?thesis using infinity_evalUni_NeqUni by auto
qed

end